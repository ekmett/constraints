{-# LANGUAGE CPP #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE Trustworthy #-}
#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 707
{-# LANGUAGE RoleAnnotations #-}
#endif
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Constraint.Forall
-- Copyright   :  (C) 2011-2015 Edward Kmett,
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  experimental
-- Portability :  non-portable
--
-- This module uses a trick to provide quantification over constraints.
----------------------------------------------------------------------------

module Data.Constraint.Forall
  ( Forall, inst
  , ForallF, instF
  , Forall1, inst1
  , ForallT, instT
  ) where

import Data.Constraint
import Data.Constraint.Unsafe

-- skolem variables, do not export!
data A
data B
-- | A quantified constraint
type Forall (p :: * -> Constraint) = (p A, p B)

type ForallF (p :: * -> Constraint) (f :: * -> *) = (p (f A), p (f B))

data F a
data M a

type Forall1 (p :: (* -> *) -> Constraint) = (p F, p M)

type ForallT (p :: * -> Constraint) (t :: (* -> *) -> * -> *) = (p (t F A), p (t M B))

#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 707
type role F nominal
type role M nominal
#endif


-- | instantiate a quantified constraint on kind @*@
inst :: forall p a. Forall p :- p a
inst = trans (unsafeCoerceConstraint :: p A :- p a) weaken1

instF :: forall p f a. ForallF p f :- p (f a)
instF = trans (unsafeCoerceConstraint :: p (f A) :- p (f a)) weaken1

-- | instantiate a quantified constraint on kind @* -> *@
inst1 :: forall (p :: (* -> *) -> Constraint) (f :: * -> *). Forall1 p :- p f
inst1 = trans (unsafeCoerceConstraint :: p F :- p f) weaken1

instT :: forall (p :: * -> Constraint) (t :: (* -> *) -> * -> *) (f :: * -> *) a. ForallT p t :- p (t f a)
instT = trans (unsafeCoerceConstraint :: p (t F A) :- p (t f a)) weaken1

