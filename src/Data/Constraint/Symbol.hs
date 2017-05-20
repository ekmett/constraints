{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
-- | Utilities for working with 'KnownSymbol' constraints.
--
-- This module is only available on GHC 8.0 or later.
module Data.Constraint.Symbol
  ( type (++)
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

type family (++) :: Symbol -> Symbol -> Symbol where
type family Take :: Nat -> Symbol -> Symbol where
type family Drop :: Nat -> Symbol -> Symbol where
type family Length :: Symbol -> Nat where

-- implementation details

setKnownSymbol :: forall n. String -> Dict (KnownSymbol n)
setKnownSymbol x = case someSymbolVal x of
                    SomeSymbol (_ :: Proxy sn) -> unsafeCoerce $ (Dict :: Dict (KnownSymbol sn))

deriveKnownSymbolNSS :: forall n m o. (Int -> String -> String) -> (KnownNat n, KnownSymbol m) :- KnownSymbol o
deriveKnownSymbolNSS f = Sub $ setKnownSymbol (fromIntegral (natVal (Proxy :: Proxy n)) `f` symbolVal (Proxy :: Proxy m))

deriveKnownSymbolSSS :: forall n m o. (String -> String -> String) -> (KnownSymbol n, KnownSymbol m) :- KnownSymbol o
deriveKnownSymbolSSS f = Sub $ setKnownSymbol (symbolVal (Proxy :: Proxy n) `f` symbolVal (Proxy :: Proxy m))

deriveKnownNatSN :: forall a n. (String -> Int) -> KnownSymbol a :- KnownNat n
deriveKnownNatSN f = Sub $ case someNatVal (toInteger (f (symbolVal (Proxy :: Proxy a)))) of
                            Just (SomeNat (_ :: Proxy sn)) -> unsafeCoerce $ (Dict :: Dict (KnownNat sn))
                            Nothing -> error "Negative natural-numbers are naturally not allowed."

axiom :: forall a b. Dict (a ~ b)
axiom = unsafeCoerce (Dict :: Dict (a ~ a))

-- axioms and operations

appendSymbol :: (KnownSymbol a, KnownSymbol b) :- KnownSymbol (a ++ b)
appendSymbol = deriveKnownSymbolSSS (++)

appendUnit1 :: forall a. Dict (("" ++ a) ~ a)
appendUnit1 = axiom

appendUnit2 :: forall a. Dict ((a ++ "") ~ a)
appendUnit2 = axiom

appendAssociates :: forall a b c. Dict (((a ++ b) ++ c) ~ (a ++ (b ++ c)))
appendAssociates = axiom

takeSymbol :: forall n a. (KnownNat n, KnownSymbol a) :- KnownSymbol (Take n a)
takeSymbol = deriveKnownSymbolNSS take

dropSymbol :: forall n a. (KnownNat n, KnownSymbol a) :- KnownSymbol (Drop n a)
dropSymbol = deriveKnownSymbolNSS drop

takeAppendDrop :: forall n a. Dict (Take n a ++ Drop n a ~ a)
takeAppendDrop = axiom

lengthSymbol :: forall a. KnownSymbol a :- KnownNat (Length a)
lengthSymbol = deriveKnownNatSN length

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
