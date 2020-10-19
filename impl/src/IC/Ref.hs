{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

{-|
This module implements the main abstract logic of the Internet Computer. It
assumes a pure and abstracted view on Canisters (provided by "IC.Canister"),
and deals with abstract requests ('AsyncRequest', 'SyncRequest'), so HTTP and
CBOR-level processing has already happened.
-}
module IC.Ref
  ( IC(..)
  , AsyncRequest(..)
  , callerOfAsync
  , SyncRequest(..)
  , RequestStatus(..)
  , CompletionValue(..)
  , ReqResponse
  , initialIC
  , authSyncRequest
  , authAsyncRequest
  , submitRequest
  , readRequest
  , runStep
  , runToCompletion
  -- $ Exported merely for debug introspection
  , CallContext(..)
  , Message(..)
  , CanState(..)
  , CallOrigin(..)
  , EntryPoint(..)
  , RunStatus(..)
  )
where

import qualified Data.Map as M
import qualified Data.Row as R
import qualified Data.Row.Variants as V
import qualified Data.ByteString.Lazy as BS
import qualified Data.Vector as Vec
import Data.Maybe
import Control.Monad.State.Class
import Control.Monad.Except
import Control.Monad.Random.Lazy
import Data.Sequence (Seq(..))
import Data.Foldable (toList)
import Codec.Candid
import Data.Row ((.==), (.+), (.!), type (.!))
import GHC.Stack

import IC.Id.Forms hiding (Blob)
import IC.Types
import IC.Funds
import IC.Canister
import qualified IC.Canister.Interface as CI
import IC.Id.Fresh
import IC.Utils
import IC.Hash
import IC.Management

-- Abstract HTTP Interface

data AsyncRequest
    = UpdateRequest Expiry CanisterId UserId MethodName Blob
  deriving (Eq, Ord, Show)

data SyncRequest
    = QueryRequest Expiry CanisterId UserId MethodName Blob
    | StatusRequest Expiry Blob

type Expiry = Timestamp

data RequestStatus
  = Unknown -- never used inside the IC, only as ReqResponse
  | Received
  | Processing
  | Rejected (RejectCode, String)
  | Completed CompletionValue
  deriving (Show)

type ReqResponse = (Bool, RequestStatus) -- Bool = True: Include timestamp

data CompletionValue -- ^ we need to be more typed than the public spec here
  = CompleteUnit
  | CompleteCanisterId CanisterId
  | CompleteArg Blob
  deriving (Show)

-- IC state

-- The canister state

data RunStatus
  = IsRunning
  | IsStopping [CallId]
  | IsStopped
  | IsDeleted -- not actually a run state, but convenient in this code
  deriving (Show)

data CanState = CanState
  { wasm_state :: Maybe WasmState   -- absent when empty
  , can_mod :: Maybe CanisterModule -- absent when empty
  , can_hash :: Maybe Blob          -- absent when empty
  , run_status :: RunStatus
  , controller :: EntityId
  , time :: Timestamp
  , balance :: Funds
  }
  deriving (Show)

-- A canister entry point is either a publicly named function, or a closure
-- (callback + environment)
data EntryPoint
  = Public MethodName Blob
  | Closure Callback Response Funds
  deriving (Show)

type CallId = Int
data CallContext = CallContext
  { canister :: CanisterId
  , origin :: CallOrigin
  , responded :: Responded
  , available_funds :: Funds
  , last_trap :: Maybe String
      -- ^ non-normative, but yields better reject messages
  }
  deriving (Show)

data CallOrigin
  = FromUser RequestID
  | FromCanister CallId Callback
  deriving (Show)

data Message
  = CallMessage
    { call_context :: CallId
    , entry :: EntryPoint
    }
  | ResponseMessage
    { call_context :: CallId
    , response :: Response
    , refunded_funds :: Funds
    }
  deriving (Show)

-- Finally, the full IC state:

data IC = IC
  { canisters :: CanisterId ↦ CanState
  , requests :: RequestID ↦ (AsyncRequest, RequestStatus)
  , messages :: Seq Message
  , call_contexts :: CallId ↦ CallContext
  , rng :: StdGen
  }
  deriving (Show)

-- The functions below want stateful access to a value of type 'IC'
type ICM m = (MonadState IC m, HasCallStack)

initialIC :: IO IC
initialIC = IC mempty mempty mempty mempty <$> newStdGen

-- Request handling

findRequest :: RequestID -> IC -> Maybe (AsyncRequest, RequestStatus)
findRequest rid ic = M.lookup rid (requests ic)

setReqStatus :: ICM m => RequestID -> RequestStatus -> m ()
setReqStatus rid s = modify $ \ic ->
  ic { requests = M.adjust (\(r,_) -> (r,s)) rid (requests ic) }

_expiryOfAsync :: AsyncRequest -> Expiry
_expiryOfAsync = \case
    UpdateRequest expiry _ _ _ _ -> expiry

_expiryOfSync :: SyncRequest -> Expiry
_expiryOfSync = \case
    QueryRequest expiry _ _ _ _ -> expiry
    StatusRequest expiry _ -> expiry

callerOfAsync :: AsyncRequest -> EntityId
callerOfAsync = \case
    UpdateRequest _ _ user_id _ _ -> user_id

callerOfRequest :: ICM m => RequestID -> m EntityId
callerOfRequest rid = gets (M.lookup rid . requests) >>= \case
    Just (ar,_) -> return (callerOfAsync ar)
    Nothing -> error "callerOfRequest"


-- Canister handling

createEmptyCanister :: ICM m => CanisterId -> EntityId -> Timestamp -> m ()
createEmptyCanister cid controller time = modify $ \ic ->
    ic { canisters = M.insert cid can (canisters ic) }
  where
    can = CanState
      { wasm_state = Nothing
      , can_mod = Nothing
      , can_hash = Nothing
      , run_status = IsRunning
      , controller = controller
      , time = time
      , balance = no_funds
      }

canisterMustExist :: (CanReject m, ICM m) => CanisterId -> m ()
canisterMustExist cid =
  gets (M.lookup cid . canisters) >>= \case
    Nothing ->
      reject RC_DESTINATION_INVALID ("canister does not exist: " ++ prettyID cid)
    Just CanState{ run_status = IsDeleted } ->
      reject RC_DESTINATION_INVALID ("canister no longer exists: " ++ prettyID cid)
    _ -> return ()

isCanisterEmpty :: (CanReject m, ICM m) => CanisterId -> m Bool
isCanisterEmpty cid = isNothing . wasm_state <$> getCanister cid


-- the following functions assume the canister does exist;
-- it would be an internal error if they dont

getCanister :: ICM m => CanisterId -> m CanState
getCanister cid =
  gets (M.lookup cid . canisters)
    `orElse` error ("canister does not exist: " ++ prettyID cid)

modCanister :: ICM m => CanisterId -> (CanState -> CanState) -> m ()
modCanister cid f = do
    void $ getCanister cid
    modify $ \ic -> ic { canisters = M.adjust f cid (canisters ic) }

setCanisterModule :: ICM m => CanisterId -> CanisterModule -> Blob -> m ()
setCanisterModule cid can_mod can_hash = modCanister cid $
    \cs -> cs { can_mod = Just can_mod, can_hash = Just can_hash }

setCanisterState :: ICM m => CanisterId -> WasmState -> m ()
setCanisterState cid wasm_state = modCanister cid $
    \cs -> cs { wasm_state = Just wasm_state }

getController :: ICM m => CanisterId -> m EntityId
getController cid = controller <$> getCanister cid

setController :: ICM m => CanisterId -> EntityId -> m ()
setController cid controller = modCanister cid $
    \cs -> cs { controller = controller }

getBalance :: ICM m => CanisterId -> m Funds
getBalance cid = balance <$> getCanister cid

setBalance :: ICM m => CanisterId -> Funds -> m ()
setBalance cid balance = modCanister cid $
    \cs -> cs { balance = balance }

getRunStatus :: ICM m => CanisterId -> m RunStatus
getRunStatus cid = run_status <$> getCanister cid

setRunStatus :: ICM m => CanisterId -> RunStatus -> m ()
setRunStatus cid run_status = modCanister cid $
    \cs -> cs { run_status = run_status }

getCanisterState :: ICM m => CanisterId -> m WasmState
getCanisterState cid = fromJust . wasm_state <$> getCanister cid

getCanisterMod :: ICM m => CanisterId -> m CanisterModule
getCanisterMod cid = fromJust . can_mod <$> getCanister cid

getCanisterTime :: ICM m => CanisterId -> m Timestamp
getCanisterTime cid = time <$> getCanister cid

-- Authentication of requests

-- This is monadic, as authentication may depend on the state of the system
-- for request status: Whether the request exists and who owns it
-- in general: eventually there will be user key management

authUser :: ICM m => Maybe PublicKey -> EntityId -> m Bool
authUser Nothing id = return $ isAnonymousId (rawEntityId id)
authUser (Just pk) id = return $ -- This is monadic to allow for key management
    isSelfAuthenticatingId pk (rawEntityId id)

authAsyncRequest :: ICM m => Maybe PublicKey -> AsyncRequest -> m Bool
authAsyncRequest pk ar = authUser pk (callerOfAsync ar)

authSyncRequest :: ICM m => Maybe PublicKey -> SyncRequest -> m Bool
authSyncRequest pk = \case
  StatusRequest _ rid ->
    gets (findRequest rid) >>= \case
      Just (ar,_) -> authUser pk (callerOfAsync ar)
      Nothing -> return False
  QueryRequest _ _ user_id _ _ ->
    authUser pk user_id

-- Synchronous requests

readRequest :: ICM m => SyncRequest -> m ReqResponse
readRequest (StatusRequest _ rid) =
  fmap (True,) $ onReject (return . Rejected) $
    gets (findRequest rid) >>= \case
      Just (_r,status) -> return status
      Nothing -> return Unknown

readRequest (QueryRequest _ canister_id user_id method arg) =
  fmap (False,) $ onReject (return . Rejected) $ do
    canisterMustExist canister_id
    getRunStatus canister_id >>= \case
       IsRunning -> return ()
       _ -> reject RC_CANISTER_ERROR "canister is stopped"
    empty <- isCanisterEmpty canister_id
    when empty $ reject RC_DESTINATION_INVALID "canister is empty"
    wasm_state <- getCanisterState canister_id
    can_mod <- getCanisterMod canister_id
    time <- getCanisterTime canister_id
    balance <- getBalance canister_id
    let env = CI.Env time balance

    f <- return (M.lookup method (query_methods can_mod))
      `orElse` reject RC_DESTINATION_INVALID "query method does not exist"

    case f user_id env arg wasm_state of
      Trap msg -> reject RC_CANISTER_ERROR $ "canister trapped: " ++ msg
      Return (Reject (rc,rm)) -> reject rc rm
      Return (Reply res) -> return $ Completed (CompleteArg res)

-- Asynchronous requests

-- | Submission simply enqueues requests

submitRequest :: ICM m => RequestID -> AsyncRequest -> m ()
submitRequest rid r = modify $ \ic ->
  if M.member rid (requests ic)
  then ic
  else ic { requests = M.insert rid (r, Received) (requests ic) }


-- | Eventually, they are processed

processRequest :: ICM m => (RequestID, AsyncRequest) -> m ()
processRequest (rid, req) = onReject (setReqStatus rid . Rejected) $ case req of
  UpdateRequest _expiry canister_id _user_id method arg -> do
    ctxt_id <- newCallContext $ CallContext
      { canister = canister_id
      , origin = FromUser rid
      , responded = Responded False
      , last_trap = Nothing
      , available_funds = no_funds
      }
    enqueueMessage $ CallMessage
      { call_context = ctxt_id
      , entry = Public method arg
      }
    setReqStatus rid Processing

-- Call context handling

newCallContext :: ICM m => CallContext -> m CallId
newCallContext cc = state $ \ic ->
  let i = freshKey (call_contexts ic)
  in (i, ic { call_contexts = M.insert i cc (call_contexts ic)})

getCallContext :: ICM m => CallId -> m CallContext
getCallContext ctxt_id = gets ((M.! ctxt_id) . call_contexts)

modifyCallContext :: ICM m => CallId -> (CallContext -> CallContext) -> m ()
modifyCallContext ctxt_id f = modify $ \ic ->
  ic { call_contexts = M.adjust f ctxt_id (call_contexts ic) }

getCallContextFunds :: ICM m => CallId -> m Funds
getCallContextFunds ctxt_id = available_funds <$> getCallContext ctxt_id

setCallContextFunds :: ICM m => CallId -> Funds -> m ()
setCallContextFunds ctxt_id funds = modifyCallContext ctxt_id $ \ctxt ->
  ctxt { available_funds = funds }

respondCallContext :: ICM m => CallId -> Response -> m ()
respondCallContext ctxt_id response = do
  ctxt <- getCallContext ctxt_id
  when (responded ctxt == Responded True) $
    error "Internal error: Double response"
  modifyCallContext ctxt_id $ \ctxt -> ctxt
    { responded = Responded True
    , available_funds = no_funds
    }
  enqueueMessage $ ResponseMessage {
    call_context = ctxt_id,
    response,
    refunded_funds = available_funds ctxt
  }

replyCallContext :: ICM m => CallId -> Blob -> m ()
replyCallContext ctxt_id blob =
  respondCallContext ctxt_id (Reply blob)

rejectCallContext :: ICM m => CallId -> (RejectCode, String) -> m ()
rejectCallContext ctxt_id r =
  respondCallContext ctxt_id (Reject r)

rememberTrap :: ICM m => CallId -> String -> m ()
rememberTrap ctxt_id msg =
  modifyCallContext ctxt_id $ \ctxt -> ctxt { last_trap = Just msg }

callerOfCallID :: ICM m => CallId -> m EntityId
callerOfCallID ctxt_id = do
  ctxt <- getCallContext ctxt_id
  case origin ctxt of
    FromUser rid -> callerOfRequest rid
    FromCanister other_ctxt_id _callback -> calleeOfCallID other_ctxt_id

calleeOfCallID :: ICM m => CallId -> m EntityId
calleeOfCallID ctxt_id = canister <$> getCallContext ctxt_id

respondedCallID :: ICM m => CallId -> m Responded
respondedCallID ctxt_id = responded <$> getCallContext ctxt_id

starveCallContext :: ICM m => CallId -> m ()
starveCallContext ctxt_id = do
  ctxt <- getCallContext ctxt_id
  let msg | Just t <- last_trap ctxt = "canister trapped: " ++ t
          | otherwise                = "canister did not respond"
  rejectCallContext ctxt_id (RC_CANISTER_ERROR, msg)

-- Message handling

enqueueMessage :: ICM m => Message -> m ()
enqueueMessage m = modify $ \ic -> ic { messages = messages ic :|> m }

processMessage :: ICM m => Message -> m ()
processMessage m = case m of
  CallMessage ctxt_id entry -> onReject (rejectCallContext ctxt_id) $ do
    callee <- calleeOfCallID ctxt_id
    if callee == managementCanisterId
    then do
      caller <- callerOfCallID ctxt_id
      rejectAsCanister $
        invokeManagementCanister caller ctxt_id entry
    else do
      canisterMustExist callee
      getRunStatus callee >>= \case
          IsRunning -> return ()
          _ -> reject RC_CANISTER_ERROR "canister is stopped"
      empty <- isCanisterEmpty callee
      when empty $ reject RC_DESTINATION_INVALID "canister is empty"
      wasm_state <- getCanisterState callee
      can_mod <- getCanisterMod callee
      time <- getCanisterTime callee
      balance <- getBalance callee
      let env = CI.Env time balance
      invokeEntry ctxt_id wasm_state can_mod env entry >>= \case
        Trap msg -> do
          -- Eventually update cycle balance here
          rememberTrap ctxt_id msg
        Return (new_state, (call_actions, canister_actions)) -> do
          performCallActions ctxt_id call_actions
          performCanisterActions callee canister_actions
          setCanisterState callee new_state

  ResponseMessage ctxt_id response refunded_funds -> do
    ctxt <- getCallContext ctxt_id
    case origin ctxt of
      FromUser rid -> setReqStatus rid $
        -- NB: Here funds disappear
        case response of
          Reject (rc, msg) -> Rejected (rc, msg)
          Reply blob -> Completed (CompleteArg blob)
      FromCanister other_ctxt_id callback -> do
        -- Add refund to balance
        cid <- calleeOfCallID other_ctxt_id
        prev_balance <- getBalance cid
        setBalance cid $ prev_balance `add_funds` refunded_funds

        enqueueMessage $ CallMessage
          { call_context = other_ctxt_id
          , entry = Closure callback response refunded_funds
          }

performCallActions :: ICM m => CallId -> CallActions -> m ()
performCallActions ctxt_id ca = do
  updateBalances ctxt_id (ca_new_calls ca) (ca_accept ca)
  mapM_ (newCall ctxt_id) (ca_new_calls ca)
  mapM_ (respondCallContext ctxt_id) (ca_response ca)


performCanisterActions :: ICM m => CanisterId -> CanisterActions -> m ()
performCanisterActions _cid _ca = return ()

updateBalances :: ICM m => CallId -> [MethodCall] -> Funds -> m ()
updateBalances ctxt_id new_calls accepted = do
  cid <- calleeOfCallID ctxt_id

  -- Eventually update when we track cycle consumption
  let max_cycles = no_funds
  let cycles_consumed = no_funds

  prev_balance <- getBalance cid
  available <- getCallContextFunds ctxt_id
  if accepted `le_funds` available
  then do
    let to_spend = prev_balance `add_funds` accepted `sub_funds` max_cycles
    let transferred = sum_funds [ call_transferred_funds c | c <- new_calls]
    if transferred `le_funds` to_spend
    then do
      setBalance cid $ prev_balance
        `add_funds` accepted
        `sub_funds` cycles_consumed
        `sub_funds` transferred
      setCallContextFunds ctxt_id $ available `sub_funds` accepted
    else error "Internal error: More funds transferred than available"
  else error "Internal error: More funds accepted than available"


managementCanisterId :: EntityId
managementCanisterId = EntityId mempty


invokeManagementCanister ::
  forall m. (CanReject m, ICM m) => EntityId -> CallId -> EntryPoint -> m ()
invokeManagementCanister caller ctxt_id (Public method_name arg) =
  case method_name of
      "create_canister" -> atomic $ icCreateCanister caller ctxt_id
      "dev_create_canister_with_funds" -> atomic $ icCreateCanisterWithFunds caller ctxt_id
      "dev_set_funds" -> atomic icDevSetFunds
      "install_code" -> atomic $ icInstallCode caller
      "set_controller" -> atomic $ icSetController caller
      "start_canister" -> atomic $ icStartCanister caller
      "stop_canister" -> deferred $ icStopCanister caller ctxt_id
      "canister_status" -> atomic $ icCanisterStatus caller
      "delete_canister" -> atomic $ icDeleteCanister caller ctxt_id
      "deposit_funds" -> atomic $ icDepositFunds caller ctxt_id
      "raw_rand" -> atomic icRawRand
      _ -> reject RC_DESTINATION_INVALID $ "Unsupported management function " ++ method_name
  where
    -- always responds
    atomic :: forall a b.  (CandidArg a, CandidArg b) => (a -> m b) -> m ()
    atomic meth = wrap (\k x -> meth x >>= k) (replyCallContext ctxt_id) arg

    -- no implict reply
    deferred :: forall a. CandidArg a => (a -> m ()) -> m ()
    deferred meth = wrap @a @() (\_k x -> meth x) (error "unused") arg

    wrap
      :: forall a b.
      (CandidArg a, CandidArg b) =>
      ((b -> m ()) -> a -> m ()) ->
      ((Blob -> m ()) -> Blob -> m ())
    wrap method raw_reply blob =
      case decode @a blob of
        Left msg -> reject RC_CANISTER_ERROR $ "Candid failed to decode: " ++ msg
        Right x -> method (raw_reply . encode @b) x

invokeManagementCanister _ _ Closure{} = error "closure invoked on management function "

icCreateCanister :: (ICM m, CanReject m) => EntityId -> CallId -> ICManagement m .! "create_canister"
icCreateCanister caller ctxt_id _r =
    icCreateCanisterWithFunds caller ctxt_id (#num_cycles .== 0 .+ #num_icpt .== 0)

icCreateCanisterWithFunds :: (ICM m, CanReject m) => EntityId -> CallId -> ICManagement m .! "dev_create_canister_with_funds"
icCreateCanisterWithFunds caller ctxt_id r = do
    -- This is for testing only
    let fake_funds = cycle_funds (r .! #num_cycles) `add_funds` icpt_funds (r .! #num_icpt)
    new_id <- gets (freshId . M.keys . canisters)
    let currentTime = 0 -- ic-ref lives in the 70ies
    createEmptyCanister new_id caller currentTime
    -- Here we fill up the canister with the funds provided by the caller
    real_funds <- getCallContextFunds ctxt_id
    setBalance new_id (fake_funds `add_funds` real_funds)
    setCallContextFunds ctxt_id no_funds
    return (#canister_id .== entityIdToPrincipal new_id)

icDevSetFunds :: (ICM m, CanReject m) => ICManagement m .! "dev_set_funds"
icDevSetFunds r = do
    -- This is for testing only
    let canister_id = principalToEntityId (r .! #canister_id)
    let fake_funds = cycle_funds (r .! #num_cycles) `add_funds` icpt_funds (r .! #num_icpt)
    canisterMustExist canister_id
    setBalance canister_id fake_funds

icInstallCode :: (ICM m, CanReject m) => EntityId -> ICManagement m .! "install_code"
icInstallCode caller r = do
    let canister_id = principalToEntityId (r .! #canister_id)
    let arg = r .! #arg
    new_can_mod <- return (parseCanister (r .! #wasm_module))
      `onErr` (\err -> reject RC_SYS_FATAL $ "Parsing failed: " ++ err)
    canisterMustExist canister_id
    checkController canister_id caller
    was_empty <- isCanisterEmpty canister_id
    time <- getCanisterTime canister_id
    balance <- getBalance canister_id
    let env = CI.Env time balance

    let
      reinstall = do
        (wasm_state, ca) <- return (init_method new_can_mod canister_id caller env arg)
          `onTrap` (\msg -> reject RC_CANISTER_ERROR $ "Initialization trapped: " ++ msg)
        setCanisterModule canister_id new_can_mod (sha256 (r .! #wasm_module))
        setCanisterState canister_id wasm_state
        performCanisterActions canister_id ca

      install = do
        unless was_empty $
          reject RC_DESTINATION_INVALID "canister is not empty during installation"
        reinstall

      upgrade = do
        when was_empty $
          reject RC_DESTINATION_INVALID "canister is empty during upgrade"
        old_wasm_state <- getCanisterState canister_id
        old_can_mod <- getCanisterMod canister_id
        (ca1, mem) <- return (pre_upgrade_method old_can_mod old_wasm_state caller env)
          `onTrap` (\msg -> reject RC_CANISTER_ERROR $ "Pre-upgrade trapped: " ++ msg)
        -- TODO: update balance in env based on ca1 here, once canister actions
        -- can change balances
        let env2 = env
        (new_wasm_state, ca2) <- return (post_upgrade_method new_can_mod canister_id caller env2 mem arg)
          `onTrap` (\msg -> reject RC_CANISTER_ERROR $ "Post-upgrade trapped: " ++ msg)

        setCanisterModule canister_id new_can_mod (sha256 (r .! #wasm_module))
        setCanisterState canister_id new_wasm_state
        performCanisterActions canister_id (ca1 <> ca2)

    R.switch (r .! #mode) $ R.empty
      .+ #install .== (\() -> install)
      .+ #reinstall .== (\() -> reinstall)
      .+ #upgrade .== (\() -> upgrade)

icSetController :: (ICM m, CanReject m) => EntityId -> ICManagement m .! "set_controller"
icSetController caller r = do
    let canister_id = principalToEntityId (r .! #canister_id)
    let new_controller = principalToEntityId (r .! #new_controller)
    canisterMustExist canister_id
    checkController canister_id caller
    setController canister_id new_controller

checkController :: (ICM m, CanReject m) => CanisterId -> EntityId -> m ()
checkController canister_id user_id = do
    controller <- getController canister_id
    unless (controller == user_id) $
      reject RC_SYS_FATAL $
        prettyID user_id <> " is not authorized to manage canister " <>
        prettyID canister_id <> ", only " <> prettyID controller <> " is"

icStartCanister :: (ICM m, CanReject m) => EntityId -> ICManagement m .! "start_canister"
icStartCanister caller r = do
    let canister_id = principalToEntityId (r .! #canister_id)
    canisterMustExist canister_id
    checkController canister_id caller
    getRunStatus canister_id >>= \case
        IsRunning -> return ()
        IsStopping pending -> forM_ pending $ \ctxt_id ->
            rejectCallContext ctxt_id (RC_CANISTER_ERROR, "Canister has been restarted")
        IsStopped -> setRunStatus canister_id IsRunning
        IsDeleted -> error "deleted canister encountered"

icStopCanister ::
  (ICM m, CanReject m) =>
  (a -> m b) ~ (ICManagement m .! "stop_canister") =>
  EntityId -> CallId -> a -> m ()
icStopCanister caller ctxt_id r = do
    let canister_id = principalToEntityId (r .! #canister_id)
    canisterMustExist canister_id
    checkController canister_id caller
    getRunStatus canister_id >>= \case
        IsRunning -> setRunStatus canister_id (IsStopping [ctxt_id])
        IsStopping pending -> setRunStatus canister_id (IsStopping (pending ++ [ctxt_id]))
        IsStopped -> replyCallContext ctxt_id (encode ())
        IsDeleted -> error "deleted canister encountered"

actuallyStopCanister :: ICM m => CanisterId -> m ()
actuallyStopCanister canister_id =
    getRunStatus canister_id >>= \case
        IsStopping pending -> do
            setRunStatus canister_id IsStopped
            forM_ pending $ \ctxt_id ->
              replyCallContext ctxt_id (Codec.Candid.encode ())
        IsRunning -> error "unexpected canister status"
        IsStopped -> error "unexpected canister status"
        IsDeleted -> error "deleted canister encountered"

icCanisterStatus :: (ICM m, CanReject m) => EntityId -> ICManagement m .! "canister_status"
icCanisterStatus caller r = do
    let canister_id = principalToEntityId (r .! #canister_id)
    canisterMustExist canister_id
    checkController canister_id caller
    s <- getRunStatus canister_id >>= \case
        IsRunning -> return (V.IsJust #running ())
        IsStopping _pending -> return (V.IsJust #stopping ())
        IsStopped -> return (V.IsJust #stopped ())
        IsDeleted -> error "deleted canister encountered"
    controller <- getController canister_id
    hash <- can_hash <$> getCanister canister_id
    funds <- getBalance canister_id
    return $ R.empty
      .+ #status .== s
      .+ #controller .== entityIdToPrincipal controller
      .+ #memory_size .== 0 -- not implemented here
      .+ #module_hash .== hash
      .+ #balance .== Vec.fromList
        -- no tuple short-hands in haskell-candid yet
        [ #_0_ .== u .+ #_1_ .== a | (u,a) <- M.toList funds, a > 0]


icDeleteCanister :: (ICM m, CanReject m) => EntityId -> CallId -> ICManagement m .! "delete_canister"
icDeleteCanister caller ctxt_id r = do
    let canister_id = principalToEntityId (r .! #canister_id)
    canisterMustExist canister_id
    checkController canister_id caller
    getRunStatus canister_id >>= \case
        IsRunning -> reject RC_SYS_FATAL "Cannot delete running canister"
        IsStopping _pending -> reject RC_SYS_FATAL "Cannot delete stopping canister"
        IsStopped -> return ()
        IsDeleted -> error "deleted canister encountered"

    funds <- getBalance canister_id
    available <- getCallContextFunds ctxt_id
    setCallContextFunds ctxt_id (available `add_funds` funds)

    setRunStatus canister_id IsDeleted

icDepositFunds :: (ICM m, CanReject m) => EntityId -> CallId -> ICManagement m .! "deposit_funds"
icDepositFunds caller ctxt_id r = do
    let canister_id = principalToEntityId (r .! #canister_id)
    canisterMustExist canister_id
    checkController canister_id caller

    funds <- getCallContextFunds ctxt_id
    available <- getCallContextFunds ctxt_id
    setCallContextFunds ctxt_id (available `sub_funds` funds)
    prev_balance <- getBalance canister_id
    setBalance canister_id $ prev_balance `add_funds` funds

icRawRand :: ICM m => ICManagement m .! "raw_rand"
icRawRand _r = runRandIC $ BS.pack <$> replicateM 32 getRandom

runRandIC :: ICM m => Rand StdGen a -> m a
runRandIC a = state $ \ic ->
    let (x, g) = runRand a (rng ic)
    in (x, ic { rng = g })

invokeEntry :: ICM m =>
    CallId -> WasmState -> CanisterModule -> CI.Env -> EntryPoint ->
    m (TrapOr (WasmState, UpdateResult))
invokeEntry ctxt_id wasm_state can_mod env entry = do
    responded <- respondedCallID ctxt_id
    available <- getCallContextFunds ctxt_id
    case entry of
      Public method dat -> do
        caller <- callerOfCallID ctxt_id
        case lookupUpdate method can_mod of
          Just f -> return $ f caller env responded available dat wasm_state
          Nothing -> do
            let reject = Reject (RC_DESTINATION_INVALID, "method does not exist: " ++ method)
            return $ Return (wasm_state, (noCallActions { ca_response = Just reject}, noCanisterActions))
      Closure cb r refund ->
        return $ callbacks can_mod cb env responded available r refund wasm_state
  where
    lookupUpdate method can_mod
        | Just f <- M.lookup method (update_methods can_mod) = Just f
        | Just f <- M.lookup method (query_methods can_mod)  = Just (asUpdate f)
        | otherwise = Nothing

newCall :: ICM m => CallId -> MethodCall -> m ()
newCall from_ctxt_id call = do
  new_ctxt_id <- newCallContext $ CallContext
    { canister = call_callee call
    , origin = FromCanister from_ctxt_id (call_callback call)
    , responded = Responded False
    , last_trap = Nothing
    , available_funds = call_transferred_funds call
    }
  enqueueMessage $ CallMessage
    { call_context = new_ctxt_id
    , entry = Public (call_method_name call) (call_arg call)
    }

-- Scheduling

-- | Pick next request in state `received`
nextReceived :: ICM m => m (Maybe (RequestID, AsyncRequest))
nextReceived = gets $ \ic -> listToMaybe
  [ (rid,r) | (rid, (r, Received)) <- M.toList (requests ic) ]

-- A call context is still waiting for a response if…
willReceiveResponse :: IC -> CallId -> Bool
willReceiveResponse ic c = c `elem`
  -- there is another call context promising to respond to this
  [ c'
  | CallContext { responded = Responded False, origin = FromCanister c' _}
      <- M.elems (call_contexts ic)
  ] ++
  -- there is an in-flight call or response message:
  [ call_context m | m <- toList (messages ic) ] ++
  -- there this canister is waiting for some canister to stop
  [ c'
  | CanState { run_status = IsStopping pending } <- M.elems (canisters ic)
  , c' <- pending
  ]
  -- NB: this could be implemented more efficient if kepts a counter of
  -- outstanding calls in each call context

-- | Find a starved call context
nextStarved :: ICM m => m (Maybe CallId)
nextStarved = gets $ \ic -> listToMaybe
  [ c
  | (c, CallContext { responded = Responded False } ) <- M.toList (call_contexts ic)
  , not $ willReceiveResponse ic c
  ]

-- | Find a canister in stopping state that is, well, stopped
nextStoppedCanister :: ICM m => m (Maybe CanisterId)
nextStoppedCanister = gets $ \ic -> listToMaybe
  [ cid
  | (cid, CanState { run_status = IsStopping _ }) <- M.toList (canisters ic)
  -- no open call context
  , null [ ()
    | (c, ctxt) <- M.toList (call_contexts ic)
    , canister ctxt == cid
    , willReceiveResponse ic c
    ]
  ]


-- | Pick (and remove) next message from queue
popMessage :: ICM m => m (Maybe Message)
popMessage = state $ \ic ->
  case messages ic of
    Empty -> (Nothing, ic)
    m :<| ms -> (Just m, ic { messages = ms })


-- | Fake time increase
bumpTime :: ICM m => m ()
bumpTime = modify $
  \ic -> ic { canisters = M.map (\cs -> cs { time = time cs +1 }) (canisters ic) }


-- | Returns true if a step was taken
runStep :: ICM m => m Bool
runStep = do
  bumpTime
  try
    [ with nextReceived processRequest
    , with popMessage processMessage
    , with nextStarved starveCallContext
    , with nextStoppedCanister actuallyStopCanister
    ]
  where
    try = foldr (\g r -> g >>= \case True -> return True; False -> r) (return False)
    with sel act = sel >>= maybe (return False) (\x -> act x >> return True)

runToCompletion :: ICM m => m ()
runToCompletion = repeatWhileTrue runStep

-- Error handling plumbing

type CanReject = MonadError (RejectCode, String)
reject :: CanReject m => RejectCode -> String -> m a2
reject code msg = throwError (code, msg)

-- To maintain the abstraction that the management canister is a canister,
-- all its errors are turned into canister errors
rejectAsCanister :: CanReject m => m a -> m a
rejectAsCanister act = catchError act (\(_c,msg) -> reject RC_CANISTER_ERROR msg)

onReject :: ICM m =>
  ((RejectCode, String) -> m b) ->
  (forall m'. (CanReject m', ICM m') => m' b) -> m b
onReject h act = runExceptT act >>= \case
  Left cs -> h cs
  Right x -> return x


onErr :: Monad m => m (Either a b) -> (a -> m b) -> m b
onErr a b = a >>= either b return

orElse :: Monad m => m (Maybe a) -> m a -> m a
orElse a b = a >>= maybe b return

onTrap :: Monad m => m (TrapOr a) -> (String -> m a) -> m a
onTrap a b = a >>= \case { Trap msg -> b msg; Return x -> return x }


