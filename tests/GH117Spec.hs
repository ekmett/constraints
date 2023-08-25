{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module GH117Spec (main, spec) where

import Test.Hspec

#if __GLASGOW_HASKELL__ >= 902
import Data.Constraint
import Data.Constraint.Char
import Data.Proxy
import GHC.TypeLits

spec :: Spec
spec =
  describe "GH #117" $ do
    it "should evaluate `charToNat @'a'` to 97" $
      case charToNat @'a' of
        Sub (Dict :: Dict (KnownNat n)) ->
          natVal (Proxy @n) `shouldBe` 97
    it "should evaluate `natToChar @97` to 'a'" $
      case natToChar @97 of
        Sub (Dict :: Dict (KnownChar c)) ->
          charVal (Proxy @c) `shouldBe` 'a'
#else
spec :: Spec
spec = return ()
#endif

main :: IO ()
main = hspec spec
