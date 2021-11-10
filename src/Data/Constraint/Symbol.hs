{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE CPP #-}
-- | Utilities for working with 'KnownSymbol' constraints.
--
-- This module is only available on GHC 8.0 or later.
module Data.Constraint.Symbol
  ( type AppendSymbol
  , type (++)
  , type Take
  , type Drop
  , type Length
  , appendSymbol
  , appendUnit1
  , appendUnit2
  , appendAssociates
  , takeSymbol
  , dropSymbol
  , takeAppendDrop
  , lengthSymbol
  , takeLength
  , take0
  , takeEmpty
  , dropLength
  , drop0
  , dropEmpty
  , lengthTake
  , lengthDrop
  , dropDrop
  , takeTake
  ) where

import Data.Constraint
import Data.Constraint.Nat
import Data.Proxy
import GHC.TypeLits
import Unsafe.Coerce

#if !(MIN_VERSION_base(4,10,0))
type family AppendSymbol (m :: Symbol) (n :: Symbol) :: Symbol
#endif

-- | An infix synonym for 'AppendSymbol'.
type (m :: Symbol) ++ (n :: Symbol) = AppendSymbol m n
infixr 5 ++

type family Take :: Nat -> Symbol -> Symbol where
type family Drop :: Nat -> Symbol -> Symbol where
type family Length :: Symbol -> Nat where

-- implementation details

newtype Magic n = Magic (KnownSymbol n => Dict (KnownSymbol n))

magicNSS :: forall n m o. (Int -> String -> String) -> (KnownNat n, KnownSymbol m) :- KnownSymbol o
magicNSS f = Sub $ unsafeCoerce (Magic Dict) (fromIntegral (natVal (Proxy :: Proxy n)) `f` symbolVal (Proxy :: Proxy m))

magicSSS :: forall n m o. (String -> String -> String) -> (KnownSymbol n, KnownSymbol m) :- KnownSymbol o
magicSSS f = Sub $ unsafeCoerce (Magic Dict) (symbolVal (Proxy :: Proxy n) `f` symbolVal (Proxy :: Proxy m))

magicSN :: forall a n. (String -> Int) -> KnownSymbol a :- KnownNat n
magicSN f = Sub $ unsafeCoerce (Magic Dict) (toInteger (f (symbolVal (Proxy :: Proxy a))))

axiom :: Dict c
axiom = unsafeCoerce (Dict :: Dict ())

-- axioms and operations

appendSymbol :: (KnownSymbol a, KnownSymbol b) :- KnownSymbol (AppendSymbol a b)
appendSymbol = magicSSS (++)

appendUnit1 :: forall a. Dict (AppendSymbol "" a ~ a)
appendUnit1 =
#if MIN_VERSION_base(4,10,0)
  Dict
#else
  axiom
#endif

appendUnit2 :: forall a. Dict (AppendSymbol a "" ~ a)
appendUnit2 =
#if MIN_VERSION_base(4,10,0)
  Dict
#else
  axiom
#endif

appendAssociates :: forall a b c. Dict (AppendSymbol (AppendSymbol a b) c ~ AppendSymbol a (AppendSymbol b c))
appendAssociates = axiom

takeSymbol :: forall n a. (KnownNat n, KnownSymbol a) :- KnownSymbol (Take n a)
takeSymbol = magicNSS take

dropSymbol :: forall n a. (KnownNat n, KnownSymbol a) :- KnownSymbol (Drop n a)
dropSymbol = magicNSS drop

takeAppendDrop :: forall n a. Dict (AppendSymbol (Take n a) (Drop n a) ~ a)
takeAppendDrop = axiom

lengthSymbol :: forall a. KnownSymbol a :- KnownNat (Length a)
lengthSymbol = magicSN length

takeLength :: forall n a. (Length a <= n) :- (Take n a ~ a)
takeLength = Sub axiom

take0 :: forall a. Dict (Take 0 a ~ "")
take0 = axiom

takeEmpty :: forall n. Dict (Take n "" ~ "")
takeEmpty = axiom

dropLength :: forall n a. (Length a <= n) :- (Drop n a ~ "")
dropLength = Sub axiom

drop0 :: forall a. Dict (Drop 0 a ~ a)
drop0 = axiom

dropEmpty :: forall n. Dict (Drop n "" ~ "")
dropEmpty = axiom

lengthTake :: forall n a. Dict (Length (Take n a) <= n)
lengthTake = axiom

lengthDrop :: forall n a. Dict (Length a <= (Length (Drop n a) + n))
lengthDrop = axiom

dropDrop :: forall n m a. Dict (Drop n (Drop m a) ~ Drop (n + m) a)
dropDrop = axiom

takeTake :: forall n m a. Dict (Take n (Take m a) ~ Take (Min n m) a)
takeTake = axiom
