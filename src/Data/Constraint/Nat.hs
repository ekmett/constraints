{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE UndecidableInstances #-}
#if __GLASGOW_HASKELL__ >= 805
{-# LANGUAGE NoStarIsType #-}
#endif
-- | Utilities for working with 'KnownNat' constraints.
--
-- This module is only available on GHC 8.0 or later.
module Data.Constraint.Nat
  ( Min, Max, Lcm, Gcd, Divides, Div, Mod
  , plusNat, minusNat, timesNat, powNat, minNat, maxNat, gcdNat, lcmNat, divNat, modNat
  , plusZero, minusZero, timesZero, timesOne, powZero, powOne, maxZero, minZero, gcdZero, gcdOne, lcmZero, lcmOne
  , plusAssociates, timesAssociates, minAssociates, maxAssociates, gcdAssociates, lcmAssociates
  , plusCommutes, timesCommutes, minCommutes, maxCommutes, gcdCommutes, lcmCommutes
  , plusDistributesOverTimes, timesDistributesOverPow, timesDistributesOverGcd, timesDistributesOverLcm
  , minDistributesOverPlus, minDistributesOverTimes, minDistributesOverPow1, minDistributesOverPow2, minDistributesOverMax
  , maxDistributesOverPlus, maxDistributesOverTimes, maxDistributesOverPow1, maxDistributesOverPow2, maxDistributesOverMin
  , gcdDistributesOverLcm, lcmDistributesOverGcd
  , minIsIdempotent, maxIsIdempotent, lcmIsIdempotent, gcdIsIdempotent
  , plusIsCancellative, timesIsCancellative
  , dividesPlus, dividesTimes, dividesMin, dividesMax, dividesPow, dividesGcd, dividesLcm
  , plusMonotone1, plusMonotone2
  , timesMonotone1, timesMonotone2
  , powMonotone1, powMonotone2
  , minMonotone1, minMonotone2
  , maxMonotone1, maxMonotone2
  , divMonotone1, divMonotone2
  , euclideanNat
  , plusMod, timesMod
  , modBound
  , dividesDef
  , timesDiv
  , eqLe, leEq, leId, leTrans
  , leZero, zeroLe
  , plusMinusInverse1, plusMinusInverse2, plusMinusInverse3
  ) where

import Data.Constraint
import Data.Proxy
import Data.Type.Bool
import GHC.TypeLits
import Unsafe.Coerce

type family Min (m::Nat) (n::Nat) :: Nat where
    Min m n = If (n <=? m) n m
type family Max (m::Nat) (n::Nat) :: Nat where
    Max m n = If (n <=? m) m n
#if !(MIN_VERSION_base(4,11,0))
type family Div (m::Nat) (n::Nat) :: Nat where
    Div m 1 = m
type family Mod (m::Nat) (n::Nat) :: Nat where
    Mod 0 m = 0
#endif
type family Gcd (m::Nat) (n::Nat) :: Nat where
    Gcd m m = m
type family Lcm (m::Nat) (n::Nat) :: Nat where
   Lcm m m = m

type Divides n m = n ~ Gcd n m

newtype Magic n = Magic (KnownNat n => Dict (KnownNat n))

magic :: forall n m o. (Integer -> Integer -> Integer) -> (KnownNat n, KnownNat m) :- KnownNat o
magic f = Sub $ unsafeCoerce (Magic Dict) (natVal (Proxy :: Proxy n) `f` natVal (Proxy :: Proxy m))

axiom :: forall a b. Dict (a ~ b)
axiom = unsafeCoerce (Dict :: Dict (a ~ a))

axiomLe :: forall (a :: Nat) (b :: Nat). Dict (a <= b)
axiomLe = axiom

eqLe :: forall (a :: Nat) (b :: Nat). (a ~ b) :- (a <= b)
eqLe = Sub Dict

dividesGcd :: forall a b c. (Divides a b, Divides a c) :- Divides a (Gcd b c)
dividesGcd = Sub axiom

dividesLcm :: forall a b c. (Divides a c, Divides b c) :- Divides (Lcm a b) c
dividesLcm = Sub axiom

gcdCommutes :: forall a b. Dict (Gcd a b ~ Gcd b a)
gcdCommutes = axiom

lcmCommutes :: forall a b. Dict (Lcm a b ~ Lcm b a)
lcmCommutes = axiom

gcdZero :: forall a. Dict (Gcd 0 a ~ a)
gcdZero = axiom

gcdOne :: forall a. Dict (Gcd 1 a ~ 1)
gcdOne = axiom

lcmZero :: forall a. Dict (Lcm 0 a ~ 0)
lcmZero = axiom

lcmOne :: forall a. Dict (Lcm 1 a ~ a)
lcmOne = axiom

gcdNat :: forall n m. (KnownNat n, KnownNat m) :- KnownNat (Gcd n m)
gcdNat = magic gcd

lcmNat :: forall n m. (KnownNat n, KnownNat m) :- KnownNat (Lcm n m)
lcmNat = magic lcm

plusNat :: forall n m. (KnownNat n, KnownNat m) :- KnownNat (n + m)
plusNat = magic (+)

minusNat :: forall n m. (KnownNat n, KnownNat m, m <= n) :- KnownNat (n - m)
minusNat = Sub $ case magic @n @m (-) of Sub r -> r

minNat   :: forall n m. (KnownNat n, KnownNat m) :- KnownNat (Min n m)
minNat = magic min

maxNat   :: forall n m. (KnownNat n, KnownNat m) :- KnownNat (Max n m)
maxNat = magic max

timesNat  :: forall n m. (KnownNat n, KnownNat m) :- KnownNat (n * m)
timesNat = magic (*)

powNat :: forall n m. (KnownNat n, KnownNat m) :- KnownNat (n ^ m)
powNat = magic (^)

divNat :: forall n m. (KnownNat n, KnownNat m, 1 <= m) :- KnownNat (Div n m)
divNat = Sub $ case magic @n @m div of Sub r -> r

modNat :: forall n m. (KnownNat n, KnownNat m, 1 <= m) :- KnownNat (Mod n m)
modNat = Sub $ case magic @n @m mod of Sub r -> r

plusZero :: forall n. Dict ((n + 0) ~ n)
plusZero = Dict

minusZero :: forall n. Dict ((n - 0) ~ n)
minusZero = Dict

timesZero :: forall n. Dict ((n * 0) ~ 0)
timesZero = Dict

timesOne :: forall n. Dict ((n * 1) ~ n)
timesOne = Dict

minZero :: forall n. Dict (Min n 0 ~ 0)
#if MIN_VERSION_base(4,16,0)
minZero = axiom
#else
minZero = Dict
#endif

maxZero :: forall n. Dict (Max n 0 ~ n)
#if MIN_VERSION_base(4,16,0)
maxZero = axiom
#else
maxZero = Dict
#endif

powZero :: forall n. Dict ((n ^ 0) ~ 1)
powZero = Dict

leZero :: forall a. (a <= 0) :- (a ~ 0)
leZero = Sub axiom

zeroLe :: forall (a :: Nat). Dict (0 <= a)
#if MIN_VERSION_base(4,16,0)
zeroLe = axiom
#else
zeroLe = Dict
#endif

plusMinusInverse1 :: forall n m. Dict (((m + n) - n) ~ m)
plusMinusInverse1 = axiom

plusMinusInverse2 :: forall n m. (m <= n) :- (((m + n) - m) ~ n)
plusMinusInverse2 = Sub axiom

plusMinusInverse3 :: forall n m. (n <= m) :- (((m - n) + n) ~ m)
plusMinusInverse3 = Sub axiom

plusMonotone1 :: forall a b c. (a <= b) :- (a + c <= b + c)
plusMonotone1 = Sub axiom

plusMonotone2 :: forall a b c. (b <= c) :- (a + b <= a + c)
plusMonotone2 = Sub axiom

powMonotone1 :: forall a b c. (a <= b) :- ((a^c) <= (b^c))
powMonotone1 = Sub axiom

powMonotone2 :: forall a b c. (b <= c) :- ((a^b) <= (a^c))
powMonotone2 = Sub axiom

divMonotone1 :: forall a b c. (a <= b) :- (Div a c <= Div b c)
divMonotone1 = Sub axiom

divMonotone2 :: forall a b c. (b <= c) :- (Div a c <= Div a b)
divMonotone2 = Sub axiom

timesMonotone1 :: forall a b c. (a <= b) :- (a * c <= b * c)
timesMonotone1 = Sub axiom

timesMonotone2 :: forall a b c. (b <= c) :- (a * b <= a * c)
timesMonotone2 = Sub axiom

minMonotone1 :: forall a b c. (a <= b) :- (Min a c <= Min b c)
minMonotone1 = Sub axiom

minMonotone2 :: forall a b c. (b <= c) :- (Min a b <= Min a c)
minMonotone2 = Sub axiom

maxMonotone1 :: forall a b c. (a <= b) :- (Max a c <= Max b c)
maxMonotone1 = Sub axiom

maxMonotone2 :: forall a b c. (b <= c) :- (Max a b <= Max a c)
maxMonotone2 = Sub axiom

powOne :: forall n. Dict ((n ^ 1) ~ n)
powOne = axiom

plusMod :: forall a b c. (1 <= c) :- (Mod (a + b) c ~ Mod (Mod a c + Mod b c) c)
plusMod = Sub axiom

timesMod :: forall a b c. (1 <= c) :- (Mod (a * b) c ~ Mod (Mod a c * Mod b c) c)
timesMod = Sub axiom

modBound :: forall m n. (1 <= n) :- (Mod m n <= n)
modBound = Sub axiom

euclideanNat :: (1 <= c) :- (a ~ (c * Div a c + Mod a c))
euclideanNat = Sub axiom

plusCommutes :: forall n m. Dict ((m + n) ~ (n + m))
plusCommutes = axiom

timesCommutes :: forall n m. Dict ((m * n) ~ (n * m))
timesCommutes = axiom

minCommutes :: forall n m. Dict (Min m n ~ Min n m)
minCommutes = axiom

maxCommutes :: forall n m. Dict (Max m n ~ Max n m)
maxCommutes = axiom

plusAssociates :: forall m n o. Dict (((m + n) + o) ~ (m + (n + o)))
plusAssociates = axiom

timesAssociates :: forall m n o. Dict (((m * n) * o) ~ (m * (n * o)))
timesAssociates = axiom

minAssociates :: forall m n o. Dict (Min (Min m n) o ~ Min m (Min n o))
minAssociates = axiom

maxAssociates :: forall m n o. Dict (Max (Max m n) o ~ Max m (Max n o))
maxAssociates = axiom

gcdAssociates :: forall a b c. Dict (Gcd (Gcd a b) c  ~ Gcd a (Gcd b c))
gcdAssociates = axiom

lcmAssociates :: forall a b c. Dict (Lcm (Lcm a b) c ~ Lcm a (Lcm b c))
lcmAssociates = axiom

minIsIdempotent :: forall n. Dict (Min n n ~ n)
minIsIdempotent = Dict

maxIsIdempotent :: forall n. Dict (Max n n ~ n)
maxIsIdempotent = Dict

gcdIsIdempotent :: forall n. Dict (Gcd n n ~ n)
gcdIsIdempotent = Dict

lcmIsIdempotent :: forall n. Dict (Lcm n n ~ n)
lcmIsIdempotent = Dict

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

timesDistributesOverGcd :: forall n m o. Dict ((n * Gcd m o) ~ Gcd (n * m) (n * o))
timesDistributesOverGcd = axiom

timesDistributesOverLcm :: forall n m o. Dict ((n * Lcm m o) ~ Lcm (n * m) (n * o))
timesDistributesOverLcm = axiom

plusIsCancellative :: forall n m o. ((n + m) ~ (n + o)) :- (m ~ o)
plusIsCancellative = Sub axiom

timesIsCancellative :: forall n m o. (1 <= n, (n * m) ~ (n * o)) :- (m ~ o)
timesIsCancellative = Sub axiom

gcdDistributesOverLcm :: forall a b c. Dict (Gcd (Lcm a b) c ~ Lcm (Gcd a c) (Gcd b c))
gcdDistributesOverLcm = axiom

lcmDistributesOverGcd :: forall a b c. Dict (Lcm (Gcd a b) c ~ Gcd (Lcm a c) (Lcm b c))
lcmDistributesOverGcd = axiom

dividesPlus :: (Divides a b, Divides a c) :- Divides a (b + c)
dividesPlus = Sub axiom

dividesTimes :: Divides a b :- Divides a (b * c)
dividesTimes = Sub axiom

dividesMin :: (Divides a b, Divides a c) :- Divides a (Min b c)
dividesMin = Sub axiom

dividesMax :: (Divides a b, Divides a c) :- Divides a (Max b c)
dividesMax = Sub axiom

-- This `dividesDef` is simpler and more convenient than Divides a b :- ((a * Div b a) ~ b)
-- because the latter can be easily derived via 'euclideanNat', but not vice versa.

dividesDef :: forall a b. Divides a b :- (Mod b a ~ 0)
dividesDef = Sub axiom

dividesPow :: (1 <= n, Divides a b) :- Divides a (b^n)
dividesPow = Sub axiom

timesDiv :: forall a b. Dict ((a * Div b a) <= b)
timesDiv = axiom

-- (<=) is an internal category in the category of constraints.

leId :: forall (a :: Nat). Dict (a <= a)
leId = Dict

leEq :: forall (a :: Nat) (b :: Nat). (a <= b, b <= a) :- (a ~ b)
leEq = Sub axiom

leTrans :: forall (a :: Nat) (b :: Nat) (c :: Nat). (b <= c, a <= b) :- (a <= c)
leTrans = Sub (axiomLe @a @c)
