{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
module GH55Spec (main, spec) where

import Test.Hspec

#if __GLASGOW_HASKELL__ >= 800
import Data.Constraint
import Data.Constraint.Nat
import GHC.TypeLits

newtype GF (n :: Nat) = GF Integer deriving (Eq, Show)

instance KnownNat n => Num (GF n) where
  xf@(GF a) + GF b = GF $ (a+b) `mod` (natVal xf)
  xf@(GF a) - GF b = GF $ (a-b) `mod` (natVal xf)
  xf@(GF a) * GF b = GF $ (a*b) `mod` (natVal xf)
  abs = id
  signum xf@(GF a) | a==0 = xf
                   | otherwise = GF 1
  fromInteger = GF

x :: GF 5
x = GF 3

y :: GF 5
y = GF 4

foo :: (KnownNat m, KnownNat n) => GF m -> GF n -> GF (Lcm m n)
foo m@(GF a) n@(GF b) = GF $ (a*b) `mod` (lcm (natVal m) (natVal n))

bar :: (KnownNat m) => GF m -> GF m -> GF m
bar (a :: GF m) b = foo a b - foo b a \\ Sub @() (lcmIsIdempotent @m) \\ lcmNat @m @m

z :: GF 5
z = bar x y

spec :: Spec
spec = describe "GH #53" $
         it "should normalize Lcm m m" $
           z `shouldBe` (GF 0 :: GF (Lcm 5 5))
#else
spec :: Spec
spec = return ()
#endif

main :: IO ()
main = hspec spec
