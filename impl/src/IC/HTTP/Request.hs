{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}
{- | Parses/produces generic requests -}
module IC.HTTP.Request where

import qualified Data.Text as T
import qualified Data.ByteString.Lazy as BS
import Control.Monad.Except
import Data.Maybe

import IC.Types
import IC.Ref (AsyncRequest(..), SyncRequest(..),
  RequestStatus(..), CompletionValue(..))
import IC.HTTP.GenR
import IC.HTTP.GenR.Parse

dummyUserId :: EntityId
dummyUserId = EntityId $ BS.pack [0xCA, 0xFF, 0xEE]

stripEnvelope :: GenR -> Either T.Text GenR
stripEnvelope = record $ do
    _ <- field blob "sender_pubkey"
    _ <- field blob "sender_sig"
    field anyType "content"

-- Parsing requests to /submit
asyncRequest :: GenR -> Either T.Text AsyncRequest
asyncRequest = record $ do
    t <- field text "request_type"
    _ <- optionalField blob "nonce"
    case t of
        "create_canister" -> do
            sender <- EntityId <$> field blob "sender"
            desired_id <- fmap EntityId <$> optionalField blob "desired_id"
            return $ CreateRequest sender desired_id
        "install_code" -> do
            cid <- EntityId <$> field blob "canister_id"
            sender <- EntityId <$> field blob "sender"
            mod <- field blob "module"
            arg <- field blob "arg"
            _ <- optionalField percentage "compute_allocation"
            mode <- fromMaybe "install" <$> optionalField text "mode"
            case mode of
                "install" -> return $ InstallRequest cid sender mod arg False
                "reinstall" -> return $ InstallRequest cid sender mod arg True
                "upgrade" -> return $ UpgradeRequest cid sender mod arg
                _ -> throwError $ "mode field should be one of install, reinstall, upgrade, not " <> T.pack (show mode)
        "call" -> do
            cid <- EntityId <$> field blob "canister_id"
            sender <- EntityId <$> field blob "sender"
            method_name <- field text "method_name"
            arg <- field blob "arg"
            return $ UpdateRequest cid sender (T.unpack method_name) arg
        _ -> throwError $ "Unknown request type \"" <> t <> "\""

-- Parsing requests to /response
syncRequest :: GenR -> Either T.Text SyncRequest
syncRequest = record $ do
    t <- field text "request_type"
    case t of
        "request_status" -> do
            rid <- field blob "request_id"
            return $ StatusRequest rid
        "query" -> do
            cid <- EntityId <$> field blob "canister_id"
            sender <- EntityId <$> field blob "sender"
            method_name <- field text "method_name"
            arg <- field blob "arg"
            return $ QueryRequest cid sender (T.unpack method_name) arg
        _ -> throwError $ "Unknown request type \"" <> t <> "\""

-- Printing responses
response :: RequestStatus -> GenR
response = \case
    Unknown -> rec ["status" =: GText "unknown"]
    Received -> rec ["status" =: GText "received"]
    Processing -> rec ["status" =: GText "processing"]
    Rejected (c, s) -> rec
        [ "status" =: GText "rejected"
        , "reject_code" =: GNat (fromIntegral (rejectCode c))
        , "reject_message" =: GText (T.pack s)
        ]
    Completed r -> rec
        [ "status" =: GText "replied"
        , "reply" =: case r of
            CompleteUnit ->
                rec []
            CompleteCanisterId id ->
                rec [ "canister_id" =: GBlob (BS.toStrict (rawEntityId id)) ]
            CompleteArg blob ->
                rec [ "arg" =: GBlob (BS.toStrict blob) ]
        ]
