{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE Trustworthy #-}
module Data.Constraint.Nat
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

axiomLe :: forall a b. Dict (a <= b)
axiomLe = axiom

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

plusZero :: forall n. Dict ((n + 0) ~ n)
plusZero = axiom

timesZero :: forall n. Dict ((n * 0) ~ 0)
timesZero = axiom

timesOne :: forall n. Dict ((n * 1) ~ n)
timesOne = axiom

minZero :: forall n. Dict (Min n 0 ~ 0)
minZero = axiom

maxZero :: forall n. Dict (Max n 0 ~ n)
maxZero = axiom

powZero :: forall n. Dict ((n ^ 0) ~ 1)
powZero = axiom

powOne :: forall n. Dict ((n ^ 1) ~ n)
powOne = axiom

plusCommutes :: forall n m. Dict ((m + n) ~ (n + m))
plusCommutes = axiom

timesCommutes :: forall n m. Dict ((m * n) ~ (n * m))
timesCommutes = axiom

minCommutes :: forall n m. Dict (Min m n ~ Min n m)
minCommutes = axiom

maxCommutes :: forall n m. Dict (Min m n ~ Min n m)
maxCommutes = axiom

plusAssociates :: forall n m o. Dict (((m + n) + o) ~ (m + (n + o)))
plusAssociates = axiom

timesAssociates :: forall n m o. Dict (((m * n) * o) ~ (m * (n * o)))
timesAssociates = axiom

minAssociates :: forall n m o. Dict (Min (Min m n) o ~ Min m (Min n o))
minAssociates = axiom

maxAssociates :: forall n m o. Dict (Max (Max m n) o ~ Max m (Max n o))
maxAssociates = axiom

minIsIdempotent :: forall n. Dict (Min n n ~ n)
minIsIdempotent = axiom

maxIsIdempotent :: forall n. Dict (Max n n ~ n)
maxIsIdempotent = axiom

minDistributesOverPlus :: forall n m o. Dict ((n + Min m o) ~ Min (n + m) (n + o))
minDistributesOverPlus = axiom

minDistributesOverTimes :: forall n m o. Dict ((n * Min m o) ~ Min (n * m) (n * o))
minDistributesOverTimes = axiom

minDistributesOverPow1 :: forall n m o. Dict ((Min n m ^ o) ~ Min (n ^ o) (m ^ o))
minDistributesOverPow1 = axiom

minDistributesOverPow2 :: forall n m o. Dict ((n ^ Min m o) ~ Min (n ^ m) (n ^ o))
minDistributesOverPow2 = axiom

minDistributesOverMax :: forall n m o. Dict (Max n (Min m o) ~ Min (Max n m) (Max n o))
minDistributesOverMax = axiom

maxDistributesOverPlus :: forall n m o. Dict ((n + Max m o) ~ Max (n + m) (n + o))
maxDistributesOverPlus = axiom

maxDistributesOverTimes :: forall n m o. Dict ((n * Max m o) ~ Max (n * m) (n * o))
maxDistributesOverTimes = axiom

maxDistributesOverPow1 :: forall n m o. Dict ((Max n m ^ o) ~ Max (n ^ o) (m ^ o))
maxDistributesOverPow1 = axiom

maxDistributesOverPow2 :: forall n m o. Dict ((n ^ Max m o) ~ Max (n ^ m) (n ^ o))
maxDistributesOverPow2 = axiom

maxDistributesOverMin :: forall n m o. Dict (Min n (Max m o) ~ Max (Min n m) (Min n o))
maxDistributesOverMin = axiom

plusDistributesOverTimes :: forall n m o. Dict ((n * (m + o)) ~ (n * m + n * o))
plusDistributesOverTimes = axiom

timesDistributesOverPow  :: forall n m o. Dict ((n ^ (m + o)) ~ (n ^ m * n ^ o))
timesDistributesOverPow = axiom

plusIsCancellative :: forall n m o. ((n + m) ~ (n + o)) :- (m ~ o)
plusIsCancellative = Sub axiom

-- (<=) is an internal category in the category of constraints.

leId :: forall a. Dict (a <= a)
leId = Dict

leEq :: forall a b. (a <= b, b <= a) :- (a ~ b)
leEq = Sub axiom

leTrans :: forall a b c. (b <= c, a <= b) :- (a <= c)
leTrans = Sub (axiomLe @a @c)
