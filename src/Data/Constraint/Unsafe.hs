{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE Unsafe #-}
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
  ) where

import Data.Coerce
import Data.Constraint
import Unsafe.Coerce

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

