{-# LANGUAGE OverloadedStrings #-}
module IC.Version where

import Data.Text
import SourceId

specVersion, implVersion :: Text
specVersion = "0.15.1"
implVersion = pack SourceId.id
