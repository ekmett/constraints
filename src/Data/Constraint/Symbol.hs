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

axiom :: forall a b. Dict (a ~ b)
axiom = unsafeCoerce (Dict :: Dict (a ~ a))

-- axioms and operations

appendSymbol :: (KnownSymbol a, KnownSymbol b) :- KnownSymbol (AppendSymbol a b)
appendSymbol = magicSSS (++)

appendUnit1 :: forall a. Dict (AppendSymbol "" a ~ a)
appendUnit1 = Dict

appendUnit2 :: forall a. Dict (AppendSymbol a "" ~ a)
appendUnit2 = Dict

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
