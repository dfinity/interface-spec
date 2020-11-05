{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE NumericUnderscores #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleContexts #-}
{- | Parses/produces generic requests -}
module IC.HTTP.Request where

import qualified Data.Text as T
import qualified Data.ByteString.Lazy as BS
import qualified Data.HashMap.Lazy as HM
import Control.Monad.Except
import Data.Time.Clock.POSIX
import Data.Bifunctor

import IC.Types
import IC.Crypto
import IC.Ref (AsyncRequest(..), SyncRequest(..),
  ReqResponse(..), CallResponse(..))
import IC.Certificate.CBOR
import IC.HTTP.RequestId
import IC.HTTP.GenR
import IC.HTTP.GenR.Parse

dummyUserId :: EntityId
dummyUserId = EntityId $ BS.pack [0xCA, 0xFF, 0xEE]

stripEnvelope :: GenR -> IO (Either T.Text (Maybe PublicKey, GenR))
stripEnvelope gr = do
    t <- getTimestamp
    return $ go t gr
  where
    go _t = record $ do
        content <- field anyType "content"
        pk <- optionalField blob "sender_pubkey"
        sig <- optionalField blob "sender_sig"
        case (pk, sig) of
            (Just pk, Just sig) -> do
                let rid = requestId content
                lift $
                    first (<> "\nExpected request id: " <> T.pack (prettyBlob rid)
                           <> "\nPublic Key:          " <> T.pack (prettyBlob pk)
                           <> "\nSignature:           " <> T.pack (prettyBlob sig)) $
                    verify "ic-request" pk rid sig
                return (Just pk, content)
            (Nothing, Nothing) -> do
                return (Nothing, content)
            _ -> throwError "Need to set either both or none of sender_pubkey and sender_sig"

getTimestamp :: IO Timestamp
getTimestamp = do
    t <- getPOSIXTime
    return $ Timestamp $ round (t * 1000_000_000)

checkExpiry :: GenR -> IO (Either T.Text ())
checkExpiry (GRec hm)
    | Just (GNat expiry) <- HM.lookup "ingress_expiry" hm = runExceptT $ do
        -- Here we check that the expiry field is not in the past and not
        -- too far in the future
        Timestamp t <- lift getTimestamp
        unless (expiry > t) $
            throwError $ "Expiry is " <> T.pack (show ((t - expiry)`div`1000_000_000)) <> " seconds in the past"
        unless (expiry < t + max_future) $
            throwError $ "Expiry is " <> T.pack (show ((expiry - t)`div`1000_000_000)) <> " seconds in the future"
  where
    -- max expiry time is 5 minutes
    max_future = 5*60*1000_000_000
checkExpiry _ = runExceptT (throwError "No ingress_expiry field found")

-- Parsing requests to /submit
asyncRequest :: GenR -> Either T.Text AsyncRequest
asyncRequest = record $ do
    t <- field text "request_type"
    _ <- optionalField blob "nonce"
    e <- Timestamp <$> field nat "ingress_expiry"
    case t of
        "call" -> do
            cid <- EntityId <$> field blob "canister_id"
            sender <- EntityId <$> field blob "sender"
            method_name <- field text "method_name"
            arg <- field blob "arg"
            return $ UpdateRequest e cid sender (T.unpack method_name) arg
        _ -> throwError $ "Unknown request type \"" <> t <> "\""

-- Parsing requests to /response
syncRequest :: GenR -> Either T.Text SyncRequest
syncRequest = record $ do
    t <- field text "request_type"
    _ <- optionalField blob "nonce"
    e <- Timestamp <$> field nat "ingress_expiry"
    case t of
        "query" -> do
            cid <- EntityId <$> field blob "canister_id"
            sender <- EntityId <$> field blob "sender"
            method_name <- field text "method_name"
            arg <- field blob "arg"
            return $ QueryRequest e cid sender (T.unpack method_name) arg
        "read_state" -> do
            sender <- EntityId <$> field blob "sender"
            paths <- field (listOf (listOf blob)) "paths"
            return $ ReadStateRequest e sender paths
        _ -> throwError $ "Unknown request type \"" <> t <> "\""

-- Printing responses
response :: ReqResponse -> GenR
response (QueryResponse (Rejected (c, s))) = rec
    [ "status" =: GText "rejected"
    , "reject_code" =: GNat (fromIntegral (rejectCode c))
    , "reject_message" =: GText (T.pack s)
    ]
response (QueryResponse (Replied blob)) = rec
    [ "status" =: GText "replied"
    , "reply" =: rec [ "arg" =: GBlob blob ]
    ]
response (ReadStateResponse cert) = rec
    [ "certificate" =: GBlob (encodeCert cert)
    ]
