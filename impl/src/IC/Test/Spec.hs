{- |

This module contains a test suite for the Internet Computer

-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE NumericUnderscores #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module IC.Test.Spec (preFlight, TestConfig, icTests) where

import qualified Data.Text as T
import qualified Data.Text.Encoding as T
import qualified Data.Text.Encoding.Error as T
import qualified Data.ByteString.Lazy as BS
import qualified Data.ByteString.Builder as BS
import qualified Data.HashMap.Lazy as HM
import Network.HTTP.Client
import Network.HTTP.Types
import Numeric.Natural
import Data.List
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.Options
import Control.Monad.Trans
import Control.Concurrent
import Control.Monad
import Control.Exception (catch)
import Data.Word
import Data.Functor
import GHC.TypeLits
import System.FilePath
import System.Directory
import System.Environment
import System.Random
import System.Exit
import Data.Time.Clock.POSIX
import Codec.Candid (Principal(..))
import qualified Codec.Candid as Candid
import Data.Row
import qualified Data.Row.Variants as V

import IC.Version
import IC.HTTP.GenR
import IC.HTTP.GenR.Parse
import IC.HTTP.CBOR (decode, encode)
import IC.HTTP.RequestId
import IC.Management
import IC.Crypto
import IC.Id.Forms hiding (Blob)
import IC.Test.Options
import IC.Test.Universal

-- * Test data, standard requests

doesn'tExist :: Blob
doesn'tExist = "\xDE\xAD\xBE\xEF" -- hopefully no such canister/user exists


defaultSK :: SecretKey
defaultSK = createSecretKey "fixed32byteseedfortesting"

otherSK :: SecretKey
otherSK = createSecretKey "anotherfixed32byteseedfortesting"

defaultUser :: Blob
defaultUser = mkSelfAuthenticatingId $ toPublicKey defaultSK
otherUser :: Blob
otherUser = mkSelfAuthenticatingId $ toPublicKey otherSK
anonymousUser :: Blob
anonymousUser = "\x04"

queryToNonExistant :: GenR
queryToNonExistant = rec
    [ "request_type" =: GText "query"
    , "canister_id" =: GBlob doesn'tExist
    , "method_name" =: GText "foo"
    , "arg" =: GBlob "nothing to see here"
    ]

requestStatusNonExistant :: GenR
requestStatusNonExistant = rec
    [ "request_type" =: GText "request_status"
    , "request_id" =: GBlob doesn'tExist
    ]


trivialWasmModule :: Blob
trivialWasmModule = "\0asm\1\0\0\0"

addIfNotThere :: Monad m => T.Text -> m GenR -> GenR -> m GenR
addIfNotThere f _ (GRec hm)| f `HM.member` hm = return (GRec hm)
addIfNotThere f a (GRec hm) = do
  x <- a
  return $ GRec $ HM.insert f x hm
addIfNotThere _ _ _ = error "addIfNotThere: not a record"

deleteField :: T.Text -> GenR -> GenR
deleteField f (GRec hm) = GRec $ HM.delete f hm
deleteField _ _ = error "deleteField: not a record"

modNatField :: T.Text -> (Natural -> Natural) -> GenR -> GenR
modNatField f g (GRec hm) = GRec $ HM.adjust underNat f hm
  where underNat :: GenR -> GenR
        underNat (GNat n) = GNat (g n)
        underNat _ = error "modNatField: not a nat field"
modNatField _ _ _ = error "modNatField: not a record"

addNonce :: GenR -> IO GenR
addNonce = addIfNotThere "nonce" $
    GBlob <$> getRand8Bytes

-- Adds expiry 1 minute
addExpiry :: GenR -> IO GenR
addExpiry = addIfNotThere "ingress_expiry" $ do
    t <- getPOSIXTime
    return $ GNat $ round ((t + 60) * 1000_000_000)

envelopeFor :: Blob -> GenR -> GenR
envelopeFor u content | u == anonymousUser = rec [ "content" =: content ]
envelopeFor u content = envelope key content
  where
    key ::  SecretKey
    key | u == defaultUser = defaultSK
        | u == otherUser = otherSK
        | u == anonymousUser = error "No key for the anonymous user"
        | otherwise = error $ "Don't know key for user " ++ show u

envelope :: SecretKey -> GenR -> GenR
envelope sk content = rec
    [ "sender_pubkey" =: GBlob (toPublicKey sk)
    , "sender_sig" =: GBlob (sign "\x0Aic-request" sk (requestId content))
    , "content" =: content
    ]

-- a little bit of smartness in our combinators

senderOf :: GenR -> Blob
senderOf (GRec hm) | Just (GBlob id) <- HM.lookup "sender" hm = id
senderOf _ = anonymousUser


badEnvelope :: GenR -> GenR
badEnvelope content = rec
    [ "sender_pubkey" =: GBlob (toPublicKey defaultSK)
    , "sender_sig" =: GBlob (BS.replicate 64 0x42)
    , "content" =: content
    ]

noDomainSepEnv :: SecretKey -> GenR -> GenR
noDomainSepEnv sk content = rec
    [ "sender_pubkey" =: GBlob (toPublicKey sk)
    , "sender_sig" =: GBlob (sign "" sk (requestId content))
    , "content" =: content
    ]

noExpiryEnv, pastExpiryEnv, futureExpiryEnv :: GenR -> GenR
noExpiryEnv = deleteField "ingress_expiry"
pastExpiryEnv = modNatField "ingress_expiry" (subtract 3600_000_000_000)
futureExpiryEnv = modNatField "ingress_expiry" (+ 3600_000_000_000)

-- * Preflight checks: Get the root key, and tell user about versions

data TestConfig = TestConfig
    { tc_manager :: Manager
    , tc_endPoint :: String
    }

preFlight :: OptionSet -> IO TestConfig
preFlight os = do
    let Endpoint ep = lookupOption os
    manager <- newManager defaultManagerSettings
    request <- parseRequest $ ep ++ "/api/v1/status"
    putStrLn $ "Fetching endpoit status from " ++ show ep ++ "..."
    s <- (httpLbs request manager >>= okCBOR >>= statusResonse)
        `catch` (\(HUnitFailure _ r) -> putStrLn r >> exitFailure)

    putStrLn $ "Spec version tested:  " ++ T.unpack specVersion
    putStrLn $ "Spec version claimed: " ++ T.unpack (status_api_version s)

    return TestConfig
        { tc_manager = manager
        , tc_endPoint = ep
        }


-- * The actual test suite (see below for helper functions)

icTests :: TestConfig -> TestTree
icTests = withTestConfig $ testGroup "Public Spec acceptance tests"
  [ simpleTestCase "create and install" $ \_ ->
      return ()

  , testCase "create_canister necessary" $
      ic_install' ic00 (enum #install) doesn'tExist trivialWasmModule ""
          >>= isReject [3,5]

  , testCaseSteps "management requests" $ \step -> do
      step "Create"
      can_id <- ic_create ic00

      step "Install"
      ic_install ic00 (enum #install) can_id trivialWasmModule ""

      step "Install again fails"
      ic_install' ic00 (enum #install) can_id trivialWasmModule ""
        >>= isReject [3,5]

      step "Reinstall"
      ic_install ic00 (enum #reinstall) can_id trivialWasmModule ""

      step "Reinstall as wrong user"
      ic_install' (ic00as otherUser) (enum #reinstall) can_id trivialWasmModule ""
        >>= isReject [3,5]

      step "Upgrade"
      ic_install ic00 (enum #upgrade) can_id trivialWasmModule ""

      step "Change controller"
      ic_set_controller ic00 can_id otherUser

      step "Change controller (with wrong controller)"
      ic_set_controller' ic00 can_id otherUser
        >>= isReject [3,5]

      step "Reinstall as new controller"
      ic_install (ic00as otherUser) (enum #reinstall) can_id trivialWasmModule ""

  , testCaseSteps "reinstall on empty" $ \step -> do
      step "Create"
      can_id <- ic_create ic00

      step "Reinstall over empty canister"
      ic_install ic00 (enum #reinstall) can_id trivialWasmModule ""

  , testCaseSteps "canister lifecycle" $ \step -> do
      cid <- install noop

      step "Is running?"
      sv <- ic_canister_status ic00 cid
      V.view #running sv @?= Just ()

      step "Stop"
      ic_stop_canister ic00 cid

      step "Is stopped?"
      sv <- ic_canister_status ic00 cid
      V.view #stopped sv @?= Just ()

      step "Stop is noop"
      ic_stop_canister ic00 cid

      step "Cannot call (update)?"
      call' cid reply >>= isReject [5]

      step "Cannot call (query)?"
      query' cid reply >>= isReject [5]

      step "Start canister"
      ic_start_canister ic00 cid

      step "Is running?"
      sv <- ic_canister_status ic00 cid
      V.view #running sv @?= Just ()

      step "Can call (update)?"
      call_ cid reply

      step "Can call (query)?"
      query_ cid reply

      step "Start is noop"
      ic_start_canister ic00 cid

  , testCaseSteps "canister deletion" $ \step -> do
      cid <- install noop

      step "Deletion fails"
      ic_delete_canister' ic00 cid >>= isReject [5]

      step "Stop"
      ic_stop_canister ic00 cid

      step "Is stopped?"
      ic_canister_status ic00 cid >>= is (enum #stopped)

      step "Deletion succeeds"
      ic_delete_canister ic00 cid

      -- Disabled; such a call gets accepted (200) but
      -- then the status never shows up, which causes a timeout
      --
      -- step "Cannot call (update)?"
      -- call' cid reply >>= isReject [3]

      step "Cannot call (inter-canister)?"
      cid2 <- install noop
      do call' cid2 $ inter_update cid defArgs
        >>= isRelayReject [3]

      step "Cannot call (query)?"
      query' cid reply >>= isReject [3]

      step "Cannot query canister status"
      ic_canister_status' ic00 cid >>= isReject [3,5]

      step "Deletion fails"
      ic_delete_canister' ic00 cid >>= isReject [3,5]


  , testCaseSteps "canister lifecycle (wrong controller)" $ \step -> do
      cid <- install noop

      step "Start as wrong user"
      ic_start_canister' (ic00as otherUser) cid >>= isReject [3,5]
      step "Stop as wrong user"
      ic_stop_canister' (ic00as otherUser) cid >>= isReject [3,5]
      step "Canister Status as wrong user"
      ic_canister_status' (ic00as otherUser) cid >>= isReject [3,5]
      step "Delete as wrong user"
      ic_delete_canister' (ic00as otherUser) cid >>= isReject [3,5]


  , testCaseSteps "aaaaa-aa (inter-canister)" $ \step -> do
    -- install universal canisters to proxy the requests
    cid <- install noop
    cid2 <- install noop

    step "Create"
    can_id <- ic_create (ic00via cid)

    step "Install"
    ic_install (ic00via cid) (enum #install) can_id trivialWasmModule ""

    step "Install again fails"
    ic_install' (ic00via cid) (enum #install) can_id trivialWasmModule ""
      >>= isRelayReject [3,5]

    step "Reinstall"
    ic_install (ic00via cid) (enum #reinstall) can_id trivialWasmModule ""

    step "Reinstall as wrong user"
    ic_install' (ic00via cid2) (enum #reinstall) can_id trivialWasmModule ""
      >>= isRelayReject [3,5]

    step "Upgrade"
    ic_install (ic00via cid) (enum #upgrade) can_id trivialWasmModule ""

    step "Change controller"
    ic_set_controller (ic00via cid) can_id cid2

    step "Change controller (with wrong controller)"
    ic_set_controller' (ic00via cid) can_id cid2
      >>= isRelayReject [3,5]

    step "Reinstall as new controller"
    ic_install (ic00via cid2) (enum #reinstall) can_id trivialWasmModule ""

    step "Create"
    can_id2 <- ic_create (ic00via cid)

    step "Reinstall on empty"
    ic_install (ic00via cid) (enum #reinstall) can_id2 trivialWasmModule ""

  , simpleTestCase "randomness" $ \cid -> do
    r1 <- ic_raw_rand ic00
    r2 <- ic_raw_rand ic00
    r3 <- ic_raw_rand (ic00via cid)
    BS.length r1 @?= 32
    BS.length r2 @?= 32
    BS.length r3 @?= 32
    assertBool "random blobs are different" $ r1 /= r2
    assertBool "random blobs are different" $ r1 /= r3
    assertBool "random blobs are different" $ r2 /= r3

  , testGroup "simple calls"
    [ simpleTestCase "Call" $ \cid ->
      call cid (replyData "ABCD") >>= is "ABCD"

    , simpleTestCase "Call (query)" $ \cid -> do
      query cid (replyData "ABCD") >>= is "ABCD"

    , simpleTestCase "Call no non-existant update method" $ \cid ->
      do submitCBOR $ rec
          [ "request_type" =: GText "call"
          , "sender" =: GBlob defaultUser
          , "canister_id" =: GBlob cid
          , "method_name" =: GText "no_such_update"
          , "arg" =: GBlob ""
          ]
        >>= isReject [3]

    , simpleTestCase "Call no non-existant query method" $ \cid ->
      do readCBOR $ rec
          [ "request_type" =: GText "query"
          , "sender" =: GBlob defaultUser
          , "canister_id" =: GBlob cid
          , "method_name" =: GText "no_such_update"
          , "arg" =: GBlob ""
          ]
        >>= queryResponse >>= isReject [3]

    , simpleTestCase "reject" $ \cid ->
      call' cid (reject "ABCD") >>= isReject [4]

    , simpleTestCase "reject (query)" $ \cid ->
      query' cid (reject "ABCD") >>= isReject [4]

    , simpleTestCase "No response" $ \cid ->
      call' cid noop >>= isReject [5]

    , simpleTestCase "No response does not rollback" $ \cid -> do
      call' cid (setGlobal "FOO") >>= isReject [5]
      query cid (replyData getGlobal) >>= is "FOO"

    , simpleTestCase "No response (query)" $ \cid ->
      query' cid noop >>= isReject [5]

    , simpleTestCase "Double reply" $ \cid ->
      call' cid (reply >>> reply) >>= isReject [5]

    , simpleTestCase "Double reply (query)" $ \cid ->
      query' cid (reply >>> reply) >>= isReject [5]

    , simpleTestCase "Reply data append after reply" $ \cid ->
      call' cid (reply >>> replyDataAppend "foo") >>= isReject [5]

    , simpleTestCase "Reply data append after reject" $ \cid ->
      call' cid (reject "bar" >>> replyDataAppend "foo") >>= isReject [5]

    , simpleTestCase "Caller" $ \cid ->
      call cid (replyData caller) >>= is defaultUser

    , simpleTestCase "Caller (query)" $ \cid ->
      query cid (replyData caller) >>= is defaultUser
  ]

  , testGroup "anonymous user"
    [ {- removed to make  0.10 tests more liberal
      simpleTestCase "update, sender absent" $ \cid ->
      do submitCBOR $ rec
          [ "request_type" =: GText "call"
          , "canister_id" =: GBlob cid
          , "method_name" =: GText "update"
          , "arg" =: GBlob (run (replyData caller))
          ]
        >>= isReply >>= is anonymousUser
    , simpleTestCase "query, sender absent" $ \cid ->
      do readCBOR $ rec
          [ "request_type" =: GText "query"
          , "canister_id" =: GBlob cid
          , "method_name" =: GText "query"
          , "arg" =: GBlob (run (replyData caller))
          ]
        >>= queryResponse >>= isReply >>= is anonymousUser
    , -}
      simpleTestCase "update, sender explicit" $ \cid ->
      do submitCBOR $ rec
          [ "request_type" =: GText "call"
          , "canister_id" =: GBlob cid
          , "sender" =: GBlob anonymousUser
          , "method_name" =: GText "update"
          , "arg" =: GBlob (run (replyData caller))
          ]
        >>= isReply >>= is anonymousUser
    , simpleTestCase "query, sender explicit" $ \cid ->
      do readCBOR $ rec
          [ "request_type" =: GText "query"
          , "canister_id" =: GBlob cid
          , "sender" =: GBlob anonymousUser
          , "method_name" =: GText "query"
          , "arg" =: GBlob (run (replyData caller))
          ]
        >>= queryResponse >>= isReply >>= is anonymousUser
    ]

  , testGroup "state"
    [ simpleTestCase "set/get" $ \cid -> do
      call_ cid $ setGlobal "FOO" >>> reply
      query cid (replyData getGlobal) >>= is "FOO"

    , simpleTestCase "set/set/get" $ \cid -> do
      call_ cid $ setGlobal "FOO" >>> reply
      call_ cid $ setGlobal "BAR" >>> reply
      query cid (replyData getGlobal) >>= is "BAR"

    , simpleTestCase "resubmission" $ \cid -> do
      -- Submits the same request (same nonce) twice, checks that
      -- the IC does not act twice.
      -- (Using growing stable memory as non-idempotent action)
      callTwice' cid (ignore (stableGrow (int 1)) >>> reply) >>= isReply >>= is ""
      query cid (replyData (i2b stableSize)) >>= is "\1\0\0\0"
    ]

  , simpleTestCase "self" $ \cid ->
    query cid (replyData self) >>= is cid

  , testGroup "inter-canister calls"
    [ simpleTestCase "to nonexistant canister" $ \cid ->
      call' cid (inter_call "foo" "bar" defArgs) >>= isRelayReject [3]

    , simpleTestCase "to nonexistant method" $ \cid ->
      call' cid (inter_call cid "bar" defArgs) >>= isRelayReject [3]

    , simpleTestCase "Call from query method traps (in update call)" $ \cid ->
      callToQuery' cid (inter_query cid defArgs) >>= isReject [5]

    , simpleTestCase "Call from query method traps (in query call)" $ \cid ->
      query' cid (inter_query cid defArgs) >>= isReject [5]

    , simpleTestCase "Call from query method traps (in inter-canister-call)" $ \cid ->
      do call' cid $
          inter_call cid "query" defArgs {
            other_side = inter_query cid defArgs
          }
        >>= isRelayReject [5]

    , simpleTestCase "Self-call (to update)" $ \cid ->
      call cid (inter_update cid defArgs)
        >>= is ("Hello " <> cid <> " this is " <> cid)

    , simpleTestCase "Self-call (to query)" $ \cid -> do
      call cid (inter_query cid defArgs)
        >>= is ("Hello " <> cid <> " this is " <> cid)

    , simpleTestCase "update commits" $ \cid -> do
      call_ cid $
        setGlobal "FOO" >>>
        inter_update cid defArgs{ other_side = setGlobal "BAR" >>> reply }

      query cid (replyData getGlobal) >>= is "BAR"

    , simpleTestCase "query does not commit" $ \cid -> do
      call_ cid $
        setGlobal "FOO" >>>
        inter_query cid defArgs{ other_side = setGlobal "BAR" >>> reply }

      do query cid $ replyData getGlobal
        >>= is "FOO"

    , simpleTestCase "query no response" $ \cid ->
      do call' cid $ inter_query cid defArgs{ other_side = noop }
        >>= isRelayReject [5]

    , simpleTestCase "query double reply" $ \cid ->
      do call' cid $ inter_query cid defArgs{ other_side = reply >>> reply }
        >>= isRelayReject [5]

    , simpleTestCase "Reject code is 0 in reply" $ \cid ->
      do call' cid $ inter_query cid defArgs{ on_reply = replyData (i2b reject_code) }
        >>= isRelayReject [0]

    , simpleTestCase "traps in reply: getting reject message" $ \cid ->
      do call' cid $ inter_query cid defArgs{ on_reply = replyRejectData }
        >>= isReject [5]

    , simpleTestCase "traps in reply: getting caller" $ \cid ->
      do call' cid $ inter_query cid defArgs{ on_reply = replyData caller }
        >>= isReject [5]

    , simpleTestCase "traps in reject: getting argument" $ \cid ->
      do call' cid $
           inter_query cid defArgs{
             on_reject = replyArgData,
             other_side = reject "rejecting"
           }
        >>= isReject [5]

    , simpleTestCase "traps in reject: getting caller" $ \cid ->
      do call' cid $
          inter_query cid defArgs{
            on_reject = replyData caller,
            other_side = reject "rejecting"
          }
        >>= isReject [5]

    , simpleTestCase "Second reply in callback" $ \cid -> do
      do call cid $
          setGlobal "FOO" >>>
          replyData "First reply" >>>
          inter_query cid defArgs{
            on_reply = setGlobal "BAR" >>> replyData "Second reply",
            on_reject = setGlobal "BAZ" >>> replyRejectData
          }
        >>= is "First reply"

      -- now check that the callback trapped and did not actual change the global
      -- This check is maybe not as good as we want: There is no guarantee
      -- that the IC actually tried to process the reply message before we do
      -- this query.
      query cid (replyData getGlobal) >>= is "FOO"

    , simpleTestCase "partial reply" $ \cid ->
      do call cid $
          replyDataAppend "FOO" >>>
          inter_query cid defArgs{ on_reply = replyDataAppend "BAR" >>> reply }
        >>= is "BAR" -- check that the FOO is silently dropped

    , testGroup "two callbacks"
      [ simpleTestCase "reply after trap" $ \cid ->
        do call cid $
            inter_query cid defArgs{ on_reply = trap "first callback traps" } >>>
            inter_query cid defArgs{ on_reply = replyData "good" }
          >>= is "good"

      , simpleTestCase "trap after reply" $ \cid ->
        do call cid $
            inter_query cid defArgs{ on_reply = replyData "good" } >>>
            inter_query cid defArgs{ on_reply = trap "second callback traps" }
         >>= is "good"

      , simpleTestCase "both trap" $ \cid ->
        do call' cid $
            inter_query cid defArgs{ on_reply = trap "first callback traps" } >>>
            inter_query cid defArgs{ on_reply = trap "second callback traps" }
          >>= isReject [5]
      ]

    , simpleTestCase "Call to other canister (to update)" $ \cid -> do
      cid2 <- install noop
      do call cid $ inter_update cid2 defArgs
        >>= is ("Hello " <> cid <> " this is " <> cid2)

    , simpleTestCase "Call to other canister (to query)" $ \cid -> do
      cid2 <- install noop
      do call cid $ inter_query cid2 defArgs
        >>= is ("Hello " <> cid <> " this is " <> cid2)
    ]

  , testCaseSteps "stable memory" $ \step -> do
    cid <- install noop

    step "Stable mem size is zero"
    query cid (replyData (i2b stableSize)) >>= is "\x0\x0\x0\x0"

    step "Writing stable memory (failing)"
    call' cid (stableWrite (int 0) "FOO") >>= isReject [5]
    step "Set stable mem (failing, query)"
    query' cid (stableWrite (int 0) "FOO") >>= isReject [5]

    step "Growing stable memory"
    call cid (replyData (i2b (stableGrow (int 1)))) >>= is "\x0\x0\x0\x0"

    step "Growing stable memory again"
    call cid (replyData (i2b (stableGrow (int 1)))) >>= is "\x1\x0\x0\x0"

    step "Growing stable memory in query"
    query cid (replyData (i2b (stableGrow (int 1)))) >>= is "\x2\x0\x0\x0"

    step "Stable mem size is two"
    query cid (replyData (i2b stableSize)) >>= is "\x2\x0\x0\x0"

    step "Writing stable memory"
    call_ cid $ stableWrite (int 0) "FOO" >>> reply

    step "Writing stable memory (query)"
    query_ cid $ stableWrite (int 0) "BAR" >>> reply

    step "Reading stable memory"
    call cid (replyData (stableRead (int 0) (int 3))) >>= is "FOO"

  , testGroup "time" $
    let getTimeTwice = cat (i64tob getTime) (i64tob getTime)
        isSameTime blob = do
          assertBool "Time not 8 bytes" (BS.length blob == 2*8)
          assertBool "Time not constant" (BS.take 8 blob == BS.drop 8 blob)
    in
    [ simpleTestCase "in query" $ \cid -> do
      query cid (replyData getTimeTwice) >>= isSameTime
    , simpleTestCase "in update" $ \cid -> do
      query cid (replyData getTimeTwice) >>= isSameTime
    , testCase "in install" $ do
      cid <- install $ setGlobal getTimeTwice
      query cid (replyData getGlobal) >>= isSameTime
    , testCase "in pre_upgrade" $ do
      cid <- install $
        ignore (stableGrow (int 1)) >>>
        onPreUpgrade (callback $ stableWrite (int 0) getTimeTwice)
      query cid (replyData (stableRead (int 0) (int (2*8)))) >>= isSameTime
    , simpleTestCase "in post_upgrade" $ \cid -> do
      upgrade cid $ setGlobal getTimeTwice
      query cid (replyData getGlobal) >>= isSameTime
    ]

  , testGroup "upgrades" $
    let installForUpgrade on_pre_upgrade = install $
            setGlobal "FOO" >>>
            ignore (stableGrow (int 1)) >>>
            stableWrite (int 0) "BAR______" >>>
            onPreUpgrade (callback on_pre_upgrade)

        checkNoUpgrade cid = do
          query cid (replyData getGlobal) >>= is "FOO"
          query cid (replyData (stableRead (int 0) (int 9))) >>= is "BAR______"
    in
    [ testCase "succeeding" $ do
      -- check that the pre-upgrade hook has access to the old state
      cid <- installForUpgrade $ stableWrite (int 3) getGlobal
      checkNoUpgrade cid

      upgrade cid $ stableWrite (int 6) (stableRead (int 0) (int 3))

      query cid (replyData getGlobal) >>= is ""
      query cid (replyData (stableRead (int 0) (int 9))) >>= is "BARFOOBAR"

    , testCase "trapping in pre-upgrade" $ do
      cid <- installForUpgrade $ trap "trap in pre-upgrade"
      checkNoUpgrade cid

      upgrade' cid noop >>= isReject [5]
      checkNoUpgrade cid

    , testCase "trapping in pre-upgrade (by calling)" $ do
      cid <- installForUpgrade $ trap "trap in pre-upgrade"
      call_ cid $
        reply >>>
        onPreUpgrade (callback (
            call_simple
                (bytes cid)
                "query"
                (callback replyArgData)
                (callback replyRejectData)
                (callback noop)
        ))
      checkNoUpgrade cid

      upgrade' cid noop >>= isReject [5]
      checkNoUpgrade cid

    , testCase "trapping in pre-upgrade (by accessing arg)" $ do
      cid <- installForUpgrade $ ignore argData
      checkNoUpgrade cid

      upgrade' cid noop >>= isReject [5]
      checkNoUpgrade cid

    , testCase "trapping in post-upgrade" $ do
      cid <- installForUpgrade $ stableWrite (int 3) getGlobal
      checkNoUpgrade cid

      upgrade' cid (trap "trap in post-upgrade") >>= isReject [5]
      checkNoUpgrade cid

    , testCase "trapping in post-upgrade (by calling)" $ do
      cid <- installForUpgrade $ stableWrite (int 3) getGlobal
      checkNoUpgrade cid

      do upgrade' cid $ call_simple
          (bytes cid)
          "query"
          (callback replyArgData)
          (callback replyRejectData)
          (callback noop)
        >>= isReject [5]
      checkNoUpgrade cid
    ]

  , testGroup "reinstall"
    [ testCase "succeeding" $ do
      cid <- install $
            setGlobal "FOO" >>>
            ignore (stableGrow (int 1)) >>>
            stableWrite (int 0) "FOO______"
      query cid (replyData getGlobal) >>= is "FOO"
      query cid (replyData (stableRead (int 0) (int 9))) >>= is "FOO______"
      query cid (replyData (i2b stableSize)) >>= is "\1\0\0\0"

      reinstall cid $
        setGlobal "BAR" >>>
        ignore (stableGrow (int 2)) >>>
        stableWrite (int 0) "BAR______"

      query cid (replyData getGlobal) >>= is "BAR"
      query cid (replyData (stableRead (int 0) (int 9))) >>= is "BAR______"
      query cid (replyData (i2b stableSize)) >>= is "\2\0\0\0"

    , testCase "trapping" $ do
      cid <- install $
            setGlobal "FOO" >>>
            ignore (stableGrow (int 1)) >>>
            stableWrite (int 0) "FOO______"
      query cid (replyData getGlobal) >>= is "FOO"
      query cid (replyData (stableRead (int 0) (int 9))) >>= is "FOO______"
      query cid (replyData (i2b stableSize)) >>= is "\1\0\0\0"

      reinstall' cid (trap "Trapping the reinstallation") >>= isReject [5]

      query cid (replyData getGlobal) >>= is "FOO"
      query cid (replyData (stableRead (int 0) (int 9))) >>= is "FOO______"
      query cid (replyData (i2b stableSize)) >>= is "\1\0\0\0"
    ]

  , testGroup "debug facilities"
    [ simpleTestCase "Using debug_print" $ \cid ->
      call_ cid (debugPrint "ic-ref-test print" >>> reply)
    , simpleTestCase "Using debug_print (query)" $ \cid ->
      query_ cid $ debugPrint "ic-ref-test print" >>> reply
    , simpleTestCase "Using debug_print with invalid bounds" $ \cid ->
      query_ cid $ badPrint >>> reply
    , simpleTestCase "Explicit trap" $ \cid ->
      call' cid (trap "trapping") >>= isReject [5]
    , simpleTestCase "Explicit trap (query)" $ \cid -> do
      query' cid (trap "trapping") >>= isReject [5]
    ]

  , testCase "caller (in init)" $ do
    cid <- install $ setGlobal caller
    query cid (replyData getGlobal) >>= is defaultUser

  , testCase "self (in init)" $ do
    cid <- install $ setGlobal self
    query cid (replyData getGlobal) >>= is cid

  , testGroup "trapping in init" $
    let
      failInInit pgm = do
        cid <- ic_create ic00
        install' cid pgm >>= isReject [5]
        -- canister does not exist
        query' cid noop >>= isReject [3]
    in
    [ testCase "explicit trap" $ failInInit $ trap "trapping in install"
    , testCase "call" $ failInInit $ call_simple
        "dummy"
        "query"
        (callback replyArgData)
        (callback replyRejectData)
        (callback (
          replyDataAppend "Hello " >>>
          replyDataAppend caller >>>
          reply
        ))
    , testCase "reply" $ failInInit reply
    , testCase "reject" $ failInInit $ reject "rejecting in init"
    ]

  , testGroup "query"
    [ testGroup "required fields" $
        omitFields (envelope defaultSK queryToNonExistant) $ \req -> do
          req <- addExpiry req
          postCBOR "/api/v1/read" req >>= code4xx

    {- removed to make  0.10 tests more liberal
    , testCase "non-existing canister" $ do
        req <- addExpiry queryToNonExistant
        postCBOR "/api/v1/read" (envelopeFor anonymousUser req)
          >>= okCBOR >>= queryResponse >>= isReject [3]
    -}
    ]

  , testGroup "request_status"
    [ testGroup "required fields" $
        omitFields (envelope defaultSK requestStatusNonExistant) $ \req ->
          postCBOR "/api/v1/read" req >>= code4xx
    ]

  , testGroup "signature checking" $
    [ ("with bad signature", badEnvelope, id)
    , ("with wrong key", envelope otherSK, id)
    , ("with no domain separator", noDomainSepEnv defaultSK, id)
    , ("with no expiry", envelope defaultSK, noExpiryEnv)
    , ("with expiry in the past", envelope defaultSK, pastExpiryEnv)
    , ("with expiry in the future", envelope defaultSK, futureExpiryEnv)
    ] <&> \(name, env, mod_req) -> testGroup name
      [ simpleTestCase "in query" $ \cid -> do
        good_req <- addNonce >=> addExpiry $ rec
              [ "request_type" =: GText "query"
              , "sender" =: GBlob defaultUser
              , "canister_id" =: GBlob cid
              , "method_name" =: GText "query"
              , "arg" =: GBlob (run reply)
              ]
        readCBOR good_req >>= queryResponse >>= isReply >>= is ""

        postCBOR "/api/v1/read" (env (mod_req good_req)) >>= code4xx

      , testCase "in unknown request status" $
          postCBOR "/api/v1/read" (env (mod_req requestStatusNonExistant)) >>= code4xx

      , simpleTestCase "in call" $ \cid -> do
          good_req <- addNonce >=> addExpiry $ rec
                [ "request_type" =: GText "call"
                , "sender" =: GBlob defaultUser
                , "canister_id" =: GBlob cid
                , "method_name" =: GText "query"
                , "arg" =: GBlob (run reply)
                ]
          let req = mod_req good_req
          postCBOR "/api/v1/submit" (env req) >>= code202_or_4xx

          -- Also check that the request was not created
          ingressDelay
          getRequestStatus_or_4xx defaultUser (requestId req) >>= is UnknownStatus

          -- check that with a valid signature, this would have worked
          submitCBOR good_req >>= isReply >>= is ""

      , testCase "in request status" $ do
          req <- addNonce >=> addExpiry $ rec
                [ "request_type" =: GText "call"
                , "sender" =: GBlob defaultUser
                , "canister_id" =: GBlob ""
                , "method_name" =: GText "provisional_create_canister_with_cycles"
                , "arg" =: GBlob "DIDL\x02\x6c\x01\xd8\xa3\x8c\xa8\x0d\x01\x6e\x7d\x01\x00\x00"
                ]
          _reply <- submitCBOR req >>= isReply
          let status_req = rec
                [ "request_type" =: GText "request_status"
                , "request_id" =: GBlob (requestId req)
                ]
          status_req <- addExpiry status_req
          postCBOR "/api/v1/read" (envelope defaultSK status_req) >>= code2xx
          postCBOR "/api/v1/read" (env (mod_req status_req)) >>= code4xx

      ]
  ]

type Blob = BS.ByteString

-- * HUnit error reporting integration

-- To use IC.HTTP.CBOR with HUnit
instance Parse IO where parseError = assertFailure . T.unpack

asRight :: HasCallStack => Either T.Text a -> IO a
asRight (Left err) = assertFailure (T.unpack err)
asRight (Right gr) = return gr

-- * Requests

-- | Posting a CBOR request, returning a raw bytestring
postCBOR :: (HasCallStack, HasTestConfig) => String -> GenR -> IO (Response BS.ByteString)
postCBOR path gr = do
    request <- parseRequest $ endPoint ++ path
    request <- return $ request
      { method = "POST"
      , requestBody = RequestBodyLBS $ BS.toLazyByteString $ encode gr
      , requestHeaders = [(hContentType, "application/cbor")]
      }
    httpLbs request testManager

-- | Add envelope to CBOR request, add a nonce and expiry if it is not there,
-- post to "read", return decoded CBOR
readCBOR :: (HasCallStack, HasTestConfig) => GenR -> IO GenR
readCBOR req = do
  req <- addNonce req
  req <- addExpiry req
  postCBOR "/api/v1/read" (envelopeFor (senderOf req) req) >>= okCBOR

-- | Add envelope to CBOR, and a nonce and expiry if not there, post to
-- "submit", poll for the request response, and return decoded CBOR
submitCBOR :: (HasCallStack, HasTestConfig) => GenR -> IO ReqResponse
submitCBOR req = do
  req <- addNonce req
  req <- addExpiry req
  res <- postCBOR "/api/v1/submit" (envelopeFor (senderOf req) req)
  code202 res
  assertBool "Response body not empty" (BS.null (responseBody res))
  awaitStatus (senderOf req) (requestId req)

-- | Submits twice
submitCBORTwice :: HasTestConfig => GenR -> IO ReqResponse
submitCBORTwice req = do
  req <- addNonce req
  req <- addExpiry req
  res <- postCBOR "/api/v1/submit" (envelopeFor (senderOf req) req)
  code202 res
  res <- postCBOR "/api/v1/submit" (envelopeFor (senderOf req) req)
  code202 res
  assertBool "Response body not empty" (BS.null (responseBody res))
  awaitStatus (senderOf req) (requestId req)

data ReqResponse = Reply Blob | Reject Natural T.Text
  deriving (Eq, Show)
data ReqStatus = Processing | Pending | Responded ReqResponse | UnknownStatus
  deriving (Eq, Show)

getRequestStatus :: HasTestConfig => Blob -> Blob -> IO ReqStatus
getRequestStatus sender rid = do
    req <- addExpiry $ rec
        [ "request_type" =: GText "request_status"
        , "request_id" =: GBlob rid
        ]
    res <- postCBOR "/api/v1/read" $ envelopeFor sender req
    gr <- okCBOR res
    requestStatusReply gr

-- A hack that goes away when migrating to read_status
getRequestStatus_or_4xx :: HasTestConfig => Blob -> Blob -> IO ReqStatus
getRequestStatus_or_4xx sender rid = do
    req <- addExpiry $ rec
        [ "request_type" =: GText "request_status"
        , "request_id" =: GBlob rid
        ]
    res <- postCBOR "/api/v1/read" $ envelopeFor sender req
    let c = statusCode (responseStatus res)
    if c == 200 then do
      gr <- okCBOR res
      requestStatusReply gr
    else if 400 <= c && c < 500 then return UnknownStatus
    else assertFailure $ "Status " ++ show c ++ " is not 4xx or status unknown\n"

requestStatusReply :: GenR -> IO ReqStatus
requestStatusReply = record $ do
        s <- field text "status"
        _ <- field nat "time"
        case s of
          "unknown" -> return UnknownStatus
          "processing" -> return Processing
          "received" -> return Pending
          "replied" -> do
            b <- field (record (field blob "arg")) "reply"
            return $ Responded (Reply b)
          "rejected" -> do
            code <- field nat "reject_code"
            msg <- field text "reject_message"
            return $ Responded (Reject code msg)
          _ -> lift $ assertFailure $ "Unexpected status " ++ show s

awaitStatus :: HasTestConfig => Blob -> Blob -> IO ReqResponse
awaitStatus sender rid = loop $ pollDelay >> getRequestStatus sender rid >>= \case
    Responded x -> return $ Just x
    _ -> return Nothing
  where
    loop :: HasCallStack => IO (Maybe a) -> IO a
    loop act = go (0::Int)
      where
        go 10000 = assertFailure "Polling timed out"
        go n = act >>= \case
          Just r -> return r
          Nothing -> go (n+1)

pollDelay :: IO ()
pollDelay = threadDelay $ 10 * 1000 -- 10 milliseonds

-- How long to wait before checking if a request that should _not_ show up on
-- the system indeed did not show up
ingressDelay :: IO ()
ingressDelay = threadDelay $ 2 * 1000 * 1000 -- 2 seconds


-- * HTTP Response predicates

codePred :: HasCallStack => String -> (Int -> Bool) -> Response Blob -> IO ()
codePred expt pred response = assertBool
    ("Status " ++ show c ++ " is not " ++ expt ++ "\n" ++ msg)
    (pred c)
  where
    c = statusCode (responseStatus response)
    msg = T.unpack (T.decodeUtf8With T.lenientDecode (BS.toStrict (BS.take 200 (responseBody response))))

code2xx, code202, code4xx, code202_or_4xx  :: HasCallStack => Response BS.ByteString -> IO ()
code2xx = codePred "2xx" $ \c -> 200 <= c && c < 300
code202 = codePred "202" $ \c -> c == 202
code4xx = codePred "4xx" $ \c -> 400 <= c && c < 500
code202_or_4xx = codePred "202 or 4xx" $ \c -> c == 202 || 400 <= c && c < 500

-- * CBOR decoding

okCBOR :: HasCallStack => Response BS.ByteString -> IO GenR
okCBOR response = do
  code2xx response
  asRight $ decode $ responseBody response

-- * Response predicates and parsers

queryResponse :: GenR -> IO ReqResponse
queryResponse = record $ do
    s <- field text "status"
    case s of
      "replied" ->
        Reply <$> field (record (field blob "arg")) "reply"
      "rejected" -> do
        code <- field nat "reject_code"
        msg <- field text "reject_message"
        return $ Reject code msg
      _ -> lift $ assertFailure $ "Unexpected status " ++ show s

isReject :: HasCallStack => [Natural] -> ReqResponse -> IO ()
isReject _ (Reply _) = assertFailure "Expected reject, got reply"
isReject codes (Reject n msg) = do
  assertBool
    ("Reject code " ++ show n ++ " not in " ++ show codes ++ "\n" ++ T.unpack msg)
    (n `elem` codes)

isReply :: HasCallStack => ReqResponse -> IO Blob
isReply (Reply b) = return b
isReply (Reject n msg) =
  assertFailure $ "Unexpected reject (code " ++ show n ++ "): " ++ T.unpack msg

is :: (Eq a, Show a) => a -> a -> Assertion
is exp act = act @?= exp

-- A reject forwarded by replyRejectData
isRelayReject :: HasCallStack => [Word32] -> ReqResponse -> IO ()
isRelayReject codes r = do
  b <- isReply r
  assertBool
    ("Reject code " ++ show b ++ " not in" ++ show codes ++ "\n")
    (BS.take 4 b `elem` map (BS.toLazyByteString . BS.word32LE) codes)

data StatusResponse = StatusResponse
    { status_api_version :: T.Text
    }

statusResonse :: HasCallStack => GenR -> IO StatusResponse
statusResonse = record $ do
    v <- field text "ic_api_version"
    _ <- optionalField text "impl_source"
    _ <- optionalField text "impl_version"
    _ <- optionalField text "impl_revision"
    swallowAllFields -- More fields are explicitly allowed
    return StatusResponse {status_api_version = v}

-- * Interacting with aaaaa-aa (via HTTP)

-- how to reach the management canister
type IC00 = T.Text -> Blob -> IO ReqResponse

ic00 :: HasTestConfig => IC00
ic00 method_name arg = submitCBOR $ rec
      [ "request_type" =: GText "call"
      , "sender" =: GBlob defaultUser
      , "canister_id" =: GBlob ""
      , "method_name" =: GText method_name
      , "arg" =: GBlob arg
      ]

ic00as :: HasTestConfig => Blob -> IC00
ic00as user method_name arg = submitCBOR $ rec
      [ "request_type" =: GText "call"
      , "sender" =: GBlob user
      , "canister_id" =: GBlob ""
      , "method_name" =: GText method_name
      , "arg" =: GBlob arg
      ]

ic00via :: HasTestConfig => Blob -> IC00
ic00via cid method_name arg =
  call' cid $
    call_simple
        (bytes "") -- aaaaa-aa
        (bytes (BS.fromStrict (T.encodeUtf8 method_name)))
        (callback replyArgData)
        (callback replyRejectData)
        (bytes arg)

managementService :: HasTestConfig => IC00 -> Rec (ICManagement IO)
managementService ic00 =
  Candid.toCandidService err $ \method_name arg ->
    ic00 method_name arg >>= isReply
  where
    err s = assertFailure $ "Candid decoding error: " ++ s

ic_create :: HasTestConfig => IC00 -> IO Blob
ic_create ic00 = do
  r <- managementService ic00 .! #provisional_create_canister_with_cycles $ #amount .== Nothing
  return (rawPrincipal (r .! #canister_id))

ic_install :: HasTestConfig => IC00 -> InstallMode -> Blob -> Blob -> Blob -> IO ()
ic_install ic00 mode canister_id wasm_module arg = do
  managementService ic00 .! #install_code $ empty
    .+ #mode .== mode
    .+ #canister_id .== Principal canister_id
    .+ #wasm_module .== wasm_module
    .+ #arg .== arg
    .+ #compute_allocation .== Nothing
    .+ #memory_allocation .== Nothing

ic_set_controller :: HasTestConfig => IC00 -> Blob -> Blob -> IO ()
ic_set_controller ic00 canister_id new_controller = do
  managementService ic00 .! #set_controller $ empty
    .+ #canister_id .== Principal canister_id
    .+ #new_controller .== Principal new_controller

ic_start_canister :: HasTestConfig => IC00 -> Blob -> IO ()
ic_start_canister ic00 canister_id = do
  managementService ic00 .! #start_canister $ empty
    .+ #canister_id .== Principal canister_id

ic_stop_canister :: HasTestConfig => IC00 -> Blob -> IO ()
ic_stop_canister ic00 canister_id = do
  managementService ic00 .! #stop_canister $ empty
    .+ #canister_id .== Principal canister_id

ic_canister_status :: HasTestConfig => IC00 -> Blob -> IO RunState
ic_canister_status ic00 canister_id = do
  r <- managementService ic00 .! #canister_status $ empty
    .+ #canister_id .== Principal canister_id
  return (r .! #status)

ic_delete_canister :: HasTestConfig => IC00 -> Blob -> IO ()
ic_delete_canister ic00 canister_id = do
  managementService ic00 .! #delete_canister $ empty
    .+ #canister_id .== Principal canister_id

ic_raw_rand :: HasTestConfig => IC00 -> IO Blob
ic_raw_rand ic00 = managementService ic00 .! #raw_rand $ ()

-- Primed variants return the request
callIC' :: forall s a b.
  HasTestConfig =>
  KnownSymbol s =>
  (a -> IO b) ~ (ICManagement IO .! s) =>
  Candid.CandidArg a =>
  IC00 -> Label s -> a -> IO ReqResponse
callIC' ic00 l x = ic00 (T.pack (symbolVal l)) (Candid.encode x)

ic_install' :: HasTestConfig => IC00 -> InstallMode -> Blob -> Blob -> Blob -> IO ReqResponse
ic_install' ic00 mode canister_id wasm_module arg =
  callIC' ic00 #install_code $ empty
    .+ #mode .== mode
    .+ #canister_id .== Principal canister_id
    .+ #wasm_module .== wasm_module
    .+ #arg .== arg
    .+ #compute_allocation .== Nothing
    .+ #memory_allocation .== Nothing

ic_set_controller' :: HasTestConfig => IC00 -> Blob -> Blob -> IO ReqResponse
ic_set_controller' ic00 canister_id new_controller = do
  callIC' ic00 #set_controller $ empty
    .+ #canister_id .== Principal canister_id
    .+ #new_controller .== Principal new_controller

ic_start_canister' :: HasTestConfig => IC00 -> Blob -> IO ReqResponse
ic_start_canister' ic00 canister_id = do
  callIC' ic00 #start_canister $ empty
    .+ #canister_id .== Principal canister_id

ic_stop_canister' :: HasTestConfig => IC00 -> Blob -> IO ReqResponse
ic_stop_canister' ic00 canister_id = do
  callIC' ic00 #stop_canister $ empty
    .+ #canister_id .== Principal canister_id

ic_canister_status' :: HasTestConfig => IC00 -> Blob -> IO ReqResponse
ic_canister_status' ic00 canister_id = do
  callIC' ic00 #canister_status $ empty
    .+ #canister_id .== Principal canister_id

ic_delete_canister' :: HasTestConfig => IC00 -> Blob -> IO ReqResponse
ic_delete_canister' ic00 canister_id = do
  callIC' ic00 #delete_canister $ empty
    .+ #canister_id .== Principal canister_id


-- * Interacting with the universal canister

-- Some common operations on the universal canister
-- The primed variant (call') return the response record,
-- e.g. to check for error conditions.
-- The unprimed variant expect a reply.

install' :: (HasCallStack, HasTestConfig) => Blob -> Prog -> IO ReqResponse
install' cid prog = do
  universal_wasm <- getTestWasm "universal_canister"
  ic_install' ic00 (enum #install) cid universal_wasm (run prog)

-- Also calls create, used default 'ic00'
install :: (HasCallStack, HasTestConfig) => Prog -> IO Blob
install prog = do
    cid <- ic_create ic00
    universal_wasm <- getTestWasm "universal_canister"
    ic_install ic00 (enum #install) cid universal_wasm (run prog)
    return cid

upgrade' :: (HasCallStack, HasTestConfig) => Blob -> Prog -> IO ReqResponse
upgrade' cid prog = do
  universal_wasm <- getTestWasm "universal_canister"
  ic_install' ic00 (enum #upgrade) cid universal_wasm (run prog)

upgrade :: (HasCallStack, HasTestConfig) => Blob -> Prog -> IO ()
upgrade cid prog = do
  universal_wasm <- getTestWasm "universal_canister"
  ic_install ic00 (enum #upgrade) cid universal_wasm (run prog)

reinstall' :: (HasCallStack, HasTestConfig) => Blob -> Prog -> IO ReqResponse
reinstall' cid prog = do
  universal_wasm <- getTestWasm "universal_canister"
  ic_install' ic00 (enum #reinstall) cid universal_wasm (run prog)

reinstall :: (HasCallStack, HasTestConfig) => Blob -> Prog -> IO ()
reinstall cid prog = do
  universal_wasm <- getTestWasm "universal_canister"
  ic_install ic00 (enum #reinstall) cid universal_wasm (run prog)

callRequest :: HasTestConfig => Blob -> Prog -> GenR
callRequest cid prog = rec
    [ "request_type" =: GText "call"
    , "sender" =: GBlob defaultUser
    , "canister_id" =: GBlob cid
    , "method_name" =: GText "update"
    , "arg" =: GBlob (run prog)
    ]

callToQuery' :: (HasCallStack, HasTestConfig) => Blob -> Prog -> IO ReqResponse
callToQuery' cid prog = submitCBOR $ rec
    [ "request_type" =: GText "call"
    , "sender" =: GBlob defaultUser
    , "canister_id" =: GBlob cid
    , "method_name" =: GText "query"
    , "arg" =: GBlob (run prog)
    ]

call' :: (HasCallStack, HasTestConfig) => Blob -> Prog -> IO ReqResponse
call' cid prog = submitCBOR (callRequest cid prog)

callTwice' :: (HasCallStack, HasTestConfig) => Blob -> Prog -> IO ReqResponse
callTwice' cid prog = submitCBORTwice (callRequest cid prog)

call :: (HasCallStack, HasTestConfig) => Blob -> Prog -> IO Blob
call cid prog = call' cid prog >>= isReply

call_ :: (HasCallStack, HasTestConfig) => Blob -> Prog -> IO ()
call_ cid prog = call cid prog >>= is ""

query' :: (HasCallStack, HasTestConfig) => Blob -> Prog -> IO ReqResponse
query' cid prog =
  readCBOR >=> queryResponse $ rec
    [ "request_type" =: GText "query"
    , "sender" =: GBlob defaultUser
    , "canister_id" =: GBlob cid
    , "method_name" =: GText "query"
    , "arg" =: GBlob (run prog)
    ]

query :: (HasCallStack, HasTestConfig) => Blob -> Prog -> IO Blob
query cid prog = query' cid prog >>= isReply

query_ :: (HasCallStack, HasTestConfig) => Blob -> Prog -> IO ()
query_ cid prog = query cid prog >>= is ""

-- Shortcut for test cases that just need one canister
simpleTestCase :: HasTestConfig => String -> (Blob -> IO ()) -> TestTree
simpleTestCase name act = testCase name $ install noop >>= act

-- * Programmatic test generation

-- | Runs test once for each field with that field removed, including nested
-- fields
omitFields :: GenR -> (GenR -> Assertion) -> [TestTree]
omitFields (GRec hm) act =
    [ let hm' = HM.delete f hm
      in testCase ("omitting " ++ T.unpack f) $ act (GRec hm')
    | f <- fields
    ] ++ concat
    [ omitFields val $ \val' -> act (GRec (HM.insert f val' hm))
    | f <- fields
    , val@(GRec _) <- return $ hm HM.! f
    ]
  where fields = sort $ HM.keys hm
omitFields _ _ = error "omitFields needs a GRec"


getRand8Bytes :: IO BS.ByteString
getRand8Bytes = BS.pack <$> replicateM 8 randomIO

-- * Endpoint handling

-- Yes, implicit arguments are frowned upon. But they are also very useful.

type HasTestConfig = (?testConfig :: TestConfig)

withTestConfig :: (forall. HasTestConfig => TestTree) -> TestConfig -> TestTree
withTestConfig act tc = let ?testConfig = tc in act

testConfig :: HasTestConfig => TestConfig
testConfig = ?testConfig

endPoint :: HasTestConfig => String
endPoint = tc_endPoint testConfig

testManager :: HasTestConfig => Manager
testManager = tc_manager testConfig

-- * Test data access

getTestFile :: FilePath -> IO FilePath
getTestFile file =
    lookupEnv "IC_TEST_DATA" >>= \case
    Just fp -> return $ fp </> file
    Nothing -> do
      -- nix use
      exePath <- getExecutablePath
      let exeRelPath = takeDirectory exePath </> "../test-data"
      -- convenient for cabal new-run use
      try [ exeRelPath, "test-data", "../test-data", "impl/test-data" ]
  where
    try (d:ds) = doesFileExist (d </> file) >>= \case
      True -> return (d </> file)
      False -> try ds
    try [] = error $ "getTestDir: Could not read " ++ file ++ " from test-data/. Please consult impl/README.md"

getTestWasm :: FilePath -> IO BS.ByteString
getTestWasm base = do
  fp <- getTestFile $ base <.> "wasm"
  BS.readFile fp


-- Convenience around Data.Row.Variants used as enums

enum :: (AllUniqueLabels r, KnownSymbol l, (r .! l) ~ ()) => Label l -> Var r
enum l = V.IsJust l ()
