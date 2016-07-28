{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE Trustworthy #-}
module Data.Constraint.TypeLits
  ( Min
  , Max
  , plusNat, timesNat, powNat, minNat, maxNat
  , plusZero, timesZero, timesOne, powZero, powOne, maxZero, minZero
  , plusAssociates, timesAssociates, minAssociates, maxAssociates
  , plusCommutes, timesCommutes, minCommutes, maxCommutes
  , plusDistributesOverTimes, timesDistributesOverPow
  , minDistributesOverPlus, minDistributesOverTimes, minDistributesOverPow1, minDistributesOverPow2, minDistributesOverMax
  , maxDistributesOverPlus, maxDistributesOverTimes, maxDistributesOverPow1, maxDistributesOverPow2, maxDistributesOverMin
  , minIsIdempotent, maxIsIdempotent
  , plusIsCancellative
  , eqLe, leEq, leId, leTrans
  ) where

import Data.Constraint
import Data.Proxy
import GHC.TypeLits
import Unsafe.Coerce

type family Min (n :: Nat) (m :: Nat) :: Nat where
type family Max (n :: Nat) (m :: Nat) :: Nat where

newtype Magic n r = Magic (KnownNat n => r)

magic :: forall n m o. (Integer -> Integer -> Integer) -> (KnownNat n, KnownNat m) :- KnownNat o
magic f = Sub $ unsafeCoerce (Magic id) (natVal (Proxy :: Proxy n) `f` natVal (Proxy :: Proxy m))

axiom :: forall a b. Dict (a ~ b)
axiom = unsafeCoerce (Dict :: Dict (a ~ a))

axiomLe :: forall a b p1 p2. p1 a -> p2 b -> Dict (a <= b)
axiomLe _ _ = axiom

eqLe :: (a ~ b) :- (a <= b)
eqLe = Sub Dict

plusNat :: forall n m. (KnownNat n, KnownNat m) :- KnownNat (n + m)
plusNat = magic (+)

minNat   :: forall n m. (KnownNat n, KnownNat m) :- KnownNat (Min n m)
minNat = magic min

maxNat   :: forall n m. (KnownNat n, KnownNat m) :- KnownNat (Max n m)
maxNat = magic max

timesNat  :: forall n m. (KnownNat n, KnownNat m) :- KnownNat (n * m)
timesNat = magic (*)

powNat :: forall n m. (KnownNat n, KnownNat m) :- KnownNat (n ^ m)
powNat = magic (^)

plusZero :: forall n p1. p1 n -> Dict ((n + 0) ~ n)
plusZero _ = axiom

timesZero :: forall n p1. p1 n -> Dict ((n * 0) ~ 0)
timesZero _ = axiom

timesOne :: forall n p1. p1 n -> Dict ((n * 1) ~ n)
timesOne _ = axiom

minZero :: forall n p1. p1 n -> Dict (Min n 0 ~ 0)
minZero _ = axiom

maxZero :: forall n p1. p1 n -> Dict (Max n 0 ~ n)
maxZero _ = axiom

powZero :: forall n p1. p1 n -> Dict ((n ^ 0) ~ 1)
powZero _ = axiom

powOne :: forall n p1. p1 n -> Dict ((n ^ 1) ~ n)
powOne _ = axiom

plusCommutes :: forall n m p1 p2. p1 n -> p2 m -> Dict ((m + n) ~ (n + m))
plusCommutes _ _ = axiom

timesCommutes :: forall n m p1 p2. p1 n -> p2 m -> Dict ((m * n) ~ (n * m))
timesCommutes _ _ = axiom

minCommutes :: forall n m p1 p2. p1 n -> p2 m -> Dict (Min m n ~ Min n m)
minCommutes _ _ = axiom

maxCommutes :: forall n m p1 p2. p1 n -> p2 m -> Dict (Min m n ~ Min n m)
maxCommutes _ _ = axiom

plusAssociates :: forall n m o p1 p2 p3. p1 n -> p2 m -> p3 o -> Dict (((m + n) + o) ~ (m + (n + o)))
plusAssociates _ _ _ = axiom

timesAssociates :: forall n m o p1 p2 p3. p1 n -> p2 m -> p3 o -> Dict (((m * n) * o) ~ (m * (n * o)))
timesAssociates _ _ _ = axiom

minAssociates :: forall n m o p1 p2 p3. p1 n -> p2 m -> p3 o -> Dict (Min (Min m n) o ~ Min m (Min n o))
minAssociates _ _ _ = axiom

maxAssociates :: forall n m o p1 p2 p3. p1 n -> p2 m -> p3 o -> Dict (Max (Max m n) o ~ Max m (Max n o))
maxAssociates _ _ _ = axiom

minIsIdempotent :: forall n p1. p1 n -> Dict (Min n n ~ n)
minIsIdempotent _ = axiom

maxIsIdempotent :: forall n p1. p1 n -> Dict (Max n n ~ n)
maxIsIdempotent _ = axiom

minDistributesOverPlus :: forall n m o p1 p2 p3. p1 n -> p2 m -> p3 o -> Dict ((n + Min m o) ~ Min (n + m) (n + o))
minDistributesOverPlus _ _ _ = axiom

minDistributesOverTimes :: forall n m o p1 p2 p3. p1 n -> p2 m -> p3 o -> Dict ((n * Min m o) ~ Min (n * m) (n * o))
minDistributesOverTimes _ _ _ = axiom

minDistributesOverPow1 :: forall n m o p1 p2 p3. p1 n -> p2 m -> p3 o -> Dict ((Min n m ^ o) ~ Min (n ^ o) (m ^ o))
minDistributesOverPow1 _ _ _ = axiom

minDistributesOverPow2 :: forall n m o p1 p2 p3. p1 n -> p2 m -> p3 o -> Dict ((n ^ Min m o) ~ Min (n ^ m) (n ^ o))
minDistributesOverPow2 _ _ _ = axiom

minDistributesOverMax :: forall n m o p1 p2 p3. p1 n -> p2 m -> p3 o -> Dict (Max n (Min m o) ~ Min (Max n m) (Max n o))
minDistributesOverMax _ _ _ = axiom

maxDistributesOverPlus :: forall n m o p1 p2 p3. p1 n -> p2 m -> p3 o -> Dict ((n + Max m o) ~ Max (n + m) (n + o))
maxDistributesOverPlus _ _ _ = axiom

maxDistributesOverTimes :: forall n m o p1 p2 p3. p1 n -> p2 m -> p3 o -> Dict ((n * Max m o) ~ Max (n * m) (n * o))
maxDistributesOverTimes _ _ _ = axiom

maxDistributesOverPow1 :: forall n m o p1 p2 p3. p1 n -> p2 m -> p3 o -> Dict ((Max n m ^ o) ~ Max (n ^ o) (m ^ o))
maxDistributesOverPow1 _ _ _ = axiom

maxDistributesOverPow2 :: forall n m o p1 p2 p3. p1 n -> p2 m -> p3 o -> Dict ((n ^ Max m o) ~ Max (n ^ m) (n ^ o))
maxDistributesOverPow2 _ _ _ = axiom

maxDistributesOverMin :: forall n m o p1 p2 p3. p1 n -> p2 m -> p3 o -> Dict (Min n (Max m o) ~ Max (Min n m) (Min n o))
maxDistributesOverMin _ _ _ = axiom

plusDistributesOverTimes :: forall n m o p1 p2 p3. p1 n -> p2 m -> p3 o -> Dict ((n * (m + o)) ~ (n * m + n * o))
plusDistributesOverTimes _ _ _ = axiom

timesDistributesOverPow  :: forall n m o p1 p2 p3. p1 n -> p2 m -> p3 o -> Dict ((n ^ (m + o)) ~ (n ^ m * n ^ o))
timesDistributesOverPow _ _ _ = axiom

plusIsCancellative :: forall n m o p1 p2 p3. p1 n -> p2 m -> p3 o -> ((n + m) ~ (n + o)) :- (m ~ o)
plusIsCancellative _ _ _ = Sub axiom

-- (<=) is an internal category in the category of constraints.

leId :: forall a p1. p1 a -> Dict (a <= a)
leId _ = Dict

leEq :: forall a b p1 p2. p1 a -> p2 b -> (a <= b, b <= a) :- (a ~ b)
leEq _ _ = Sub axiom

leTrans :: forall a b c p1 p2 p3. p1 a -> p2 b -> p3 c -> (b <= c, a <= b) :- (a <= c)
leTrans _ _ _ = Sub (axiomLe (Proxy :: Proxy a) (Proxy :: Proxy c))
