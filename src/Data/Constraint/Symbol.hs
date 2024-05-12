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
import Data.Constraint.Unsafe
import Data.Proxy
import GHC.TypeLits
#if MIN_VERSION_base(4,18,0)
import qualified GHC.TypeNats as TN
#else
import Unsafe.Coerce
#endif

-- | An infix synonym for 'AppendSymbol'.
type (m :: Symbol) ++ (n :: Symbol) = AppendSymbol m n
infixr 5 ++

type family Take :: Nat -> Symbol -> Symbol where
type family Drop :: Nat -> Symbol -> Symbol where
type family Length :: Symbol -> Nat where

-- implementation details

#if !MIN_VERSION_base(4,18,0)
newtype Magic n = Magic (KnownSymbol n => Dict (KnownSymbol n))
#endif

magicNSS :: forall n m o. (Int -> String -> String) -> (KnownNat n, KnownSymbol m) :- KnownSymbol o
#if MIN_VERSION_base(4,18,0)
magicNSS f = Sub $ withKnownSymbol (unsafeSSymbol @o (fromIntegral (natVal (Proxy @n)) `f` symbolVal (Proxy @m))) Dict
#else
magicNSS f = Sub $ unsafeCoerce (Magic Dict) (fromIntegral (natVal (Proxy @n)) `f` symbolVal (Proxy @m))
#endif

magicSSS :: forall n m o. (String -> String -> String) -> (KnownSymbol n, KnownSymbol m) :- KnownSymbol o
#if MIN_VERSION_base(4,18,0)
magicSSS f = Sub $ withKnownSymbol (unsafeSSymbol @o (symbolVal (Proxy @n) `f` symbolVal (Proxy @m))) Dict
#else
magicSSS f = Sub $ unsafeCoerce (Magic Dict) (symbolVal (Proxy @n) `f` symbolVal (Proxy @m))
#endif

magicSN :: forall a n. (String -> Int) -> KnownSymbol a :- KnownNat n
#if MIN_VERSION_base(4,18,0)
magicSN f = Sub $ TN.withKnownNat (unsafeSNat @n (fromIntegral (f (symbolVal (Proxy :: Proxy a))))) Dict
#else
magicSN f = Sub $ unsafeCoerce (Magic Dict) (toInteger (f (symbolVal (Proxy @a))))
#endif

-- operations

appendSymbol :: (KnownSymbol a, KnownSymbol b) :- KnownSymbol (AppendSymbol a b)
appendSymbol = magicSSS (++)

appendUnit1 :: forall a. Dict (AppendSymbol "" a ~ a)
appendUnit1 = Dict

appendUnit2 :: forall a. Dict (AppendSymbol a "" ~ a)
appendUnit2 = Dict

appendAssociates :: forall a b c. Dict (AppendSymbol (AppendSymbol a b) c ~ AppendSymbol a (AppendSymbol b c))
appendAssociates = unsafeAxiom

takeSymbol :: forall n a. (KnownNat n, KnownSymbol a) :- KnownSymbol (Take n a)
takeSymbol = magicNSS take

dropSymbol :: forall n a. (KnownNat n, KnownSymbol a) :- KnownSymbol (Drop n a)
dropSymbol = magicNSS drop

takeAppendDrop :: forall n a. Dict (AppendSymbol (Take n a) (Drop n a) ~ a)
takeAppendDrop = unsafeAxiom

lengthSymbol :: forall a. KnownSymbol a :- KnownNat (Length a)
lengthSymbol = magicSN length

takeLength :: forall n a. (Length a <= n) :- (Take n a ~ a)
takeLength = Sub unsafeAxiom

take0 :: forall a. Dict (Take 0 a ~ "")
take0 = unsafeAxiom

takeEmpty :: forall n. Dict (Take n "" ~ "")
takeEmpty = unsafeAxiom

dropLength :: forall n a. (Length a <= n) :- (Drop n a ~ "")
dropLength = Sub unsafeAxiom

drop0 :: forall a. Dict (Drop 0 a ~ a)
drop0 = unsafeAxiom

dropEmpty :: forall n. Dict (Drop n "" ~ "")
dropEmpty = unsafeAxiom

lengthTake :: forall n a. Dict (Length (Take n a) <= n)
lengthTake = unsafeAxiom

lengthDrop :: forall n a. Dict (Length a <= (Length (Drop n a) + n))
lengthDrop = unsafeAxiom

dropDrop :: forall n m a. Dict (Drop n (Drop m a) ~ Drop (n + m) a)
dropDrop = unsafeAxiom

takeTake :: forall n m a. Dict (Take n (Take m a) ~ Take (Min n m) a)
takeTake = unsafeAxiom
