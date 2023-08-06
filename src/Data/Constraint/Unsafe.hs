{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE Unsafe #-}
{-# LANGUAGE CPP #-}
{-# OPTIONS_GHC -fno-warn-redundant-constraints #-}

-- |
-- Copyright   :  (C) 2011-2021 Edward Kmett
-- License     :  BSD-style (see the file LICENSE)
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Unsafe utilities used throughout @constraints@. As the names suggest, these
-- functions are unsafe in general and can cause your program to segfault if
-- used improperly. Handle with care.

module Data.Constraint.Unsafe
  ( Coercible
  , unsafeAxiom
  , unsafeCoerceConstraint
  , unsafeDerive
  , unsafeUnderive

#if MIN_VERSION_base(4,18,0)
    -- * Unsafely creating @GHC.TypeLits@ singleton values
  , unsafeSNat
  , unsafeSSymbol
#endif
  ) where

import Data.Coerce
import Data.Constraint
import Unsafe.Coerce

#if MIN_VERSION_base(4,18,0)
import GHC.TypeLits (SNat, SSymbol)
import Numeric.Natural (Natural)
#endif

-- | Unsafely create a dictionary for any constraint.
unsafeAxiom :: Dict c
unsafeAxiom = unsafeCoerce (Dict :: Dict ())

-- | Coerce a dictionary unsafely from one type to another
unsafeCoerceConstraint :: a :- b
unsafeCoerceConstraint = unsafeCoerce refl

-- | Coerce a dictionary unsafely from one type to a newtype of that type
unsafeDerive :: Coercible n o => (o -> n) -> t o :- t n
unsafeDerive _ = unsafeCoerceConstraint

-- | Coerce a dictionary unsafely from a newtype of a type to the base type
unsafeUnderive :: Coercible n o => (o -> n) -> t n :- t o
unsafeUnderive _ = unsafeCoerceConstraint

#if MIN_VERSION_base(4,18,0)
-- NB: if https://gitlab.haskell.org/ghc/ghc/-/issues/23478 were implemented,
-- then we could avoid using 'unsafeCoerce' in the definitions below.

-- | Unsafely create an 'SNat' value directly from a 'Natural'. Use this
-- function with care:
--
-- * The 'Natural' value must match the 'Nat' @n@ encoded in the return type
--   @'SNat' n@.
--
-- * Be wary of using this function to create multiple values of type
--   @'SNat' T@, where @T@ is a type family that does not reduce (e.g.,
--   @Any@ from "GHC.Exts"). If you do, GHC is liable to optimize away one of
--   the values and replace it with the other during a common subexpression
--   elimination pass. If the two values have different underlying 'Natural'
--   values, this could be disastrous.
unsafeSNat :: Natural -> SNat n
unsafeSNat = unsafeCoerce

-- | Unsafely create an 'SSymbol' value directly from a 'String'. Use this
-- function with care:
--
-- * The 'String' value must match the 'Symbol' @s@ encoded in the return type
--   @'SSymbol' s@.
--
-- * Be wary of using this function to create multiple values of type
--   @'SSymbol' T@, where @T@ is a type family that does not reduce (e.g.,
--   @Any@ from "GHC.Exts"). If you do, GHC is liable to optimize away one of
--   the values and replace it with the other during a common subexpression
--   elimination pass. If the two values have different underlying 'String'
--   values, this could be disastrous.
unsafeSSymbol :: String -> SSymbol s
unsafeSSymbol = unsafeCoerce
#endif
