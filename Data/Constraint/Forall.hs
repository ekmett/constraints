{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE Trustworthy #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Constraint.Forall
-- Copyright   :  (C) 2011-2012 Edward Kmett,
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  experimental
-- Portability :  non-portable
--
----------------------------------------------------------------------------

module Data.Constraint.Forall
  ( Forall, inst
  , Forall1, inst1
  ) where

import Data.Constraint
import Data.Constraint.Unsafe

-- skolem variables, do not export!
data A
data B
-- | A quantified constraint
type Forall (p :: * -> Constraint) = (p A, p B)

data F a
data M a
type Forall1 (p :: (* -> *) -> Constraint) = (p F, p M)


-- | instantiate a quantified constraint on kind @*@
inst :: forall p a. Forall p :- p a
inst = trans (unsafeCoerceConstraint :: p A :- p a) weaken1

-- | instantiate a quantified constraint on kind @* -> *@
inst1 :: forall (p :: (* -> *) -> Constraint) (f :: * -> *). Forall1 p :- p f
inst1 = trans (unsafeCoerceConstraint :: p F :- p f) weaken1

-- class Forall p where instantiate :: Dict (p a)
