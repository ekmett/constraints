{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE PolyKinds #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Constraint.Forall
-- Copyright   :  (C) 2011-2015 Edward Kmett,
--                (C) 2015 Ørjan Johansen,
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
import Unsafe.Coerce (unsafeCoerce)

{- The basic trick of this module is to use "skolem" types as test candidates
 - for whether a class predicate holds, and if so assume that it holds for all
 - types, unsafely coercing the typeclass dictionary.
 -
 - A previous version of this module used concrete, unexported types as the
 - skolems. This turned out to be unsound in the presence of type families.
 - There were 3 somewhat distinct issues:
 -
 - 1. Using closed type families, it is possible to test whether two concrete
 - types are equal, even if one of them is not directly importable.
 -
 - 2. Using just open type families, it is possible to test "at least 2 of
 - these n+1 types are equal", thus using the pigeonhole principle to thwart
 - any scheme based on having only a finite number of shared skolem types.
 -
 - 3. Using just pattern matching of types by unification, it is possible
 - to extract the skolem types from the application the `Forall p` expands
 - to. (Although type families are probably still needed to exploit this.)
 -
 - András Kovács and Ørjan Johansen independently realized that skolems
 - themselves made as type family applications can be used to solve the first
 - two problems (and discovered the third problem in the process). As a bonus,
 - the resulting code is easy to make polykinded.
 -
 - Problem 1 is solved by making the type family have no instances, forcing
 - GHC to make no assumption about what type a skolem is.
 -
 - Problem 2 is solved by parametrizing the skolem on the predicate tested
 - for. (This is a known trick in predicate logic.)
 -
 - Problem 3 is solved by making the `Forall p` application expand to a type
 - class, and have the *actual* test constraint be a superclass constraint on
 - that type class, thus preventing the user directly accessing it.
 -
 - An unfortunate side effect of the new method is that it tends to trigger
 - spurious errors from GHC test for cycles in superclass constraints. András
 - Kovács discovered that these can be silenced by yet another use of a type
 - family.
 -
 - David Feuer points out a remaining doubt about the soundness of this scheme:
 - GHC *does* know that the skolems created from a single predicate `p` are
 - equal. This could in theory apply even if the skolems come from two
 - *distinct* invocations of `Forall p`.
 -
 - However, we don't know any way of bringing two such skolems in contact with
 - each other to create an actual exploit. It would seem to require `p` to
 - already contain its own skolem, despite there being (hopefully) no way to
 - extract it from `Forall p` in order to tie the knot.
 -}

-- the `Skolem*` type families represent skolem variables, do not export!
-- if GHC supports it, these might be made closed with no instances.

type family Skolem (p :: k -> Constraint) :: k
type family SkolemF (p :: k2 -> Constraint) (f :: k1 -> k2) :: k1
type family SkolemT1 (p :: k3 -> Constraint) (t :: k1 -> k2 -> k3) :: k1
type family SkolemT2 (p :: k3 -> Constraint) (t :: k1 -> k2 -> k3) :: k2

-- The outer `Forall*` type families prevent GHC from giving a spurious
-- superclass cycle error.
-- The inner `Forall*_` classes prevent the skolem from leaking to the user,
-- which would be disastrous.

-- | A representation of the quantified constraint @forall a. p a@.
type family Forall (p :: k -> Constraint) :: Constraint
type instance Forall p = Forall_ p
class p (Skolem p) => Forall_ (p :: k -> Constraint)
instance p (Skolem p) => Forall_ (p :: k -> Constraint)

-- | A representation of the quantified constraint @forall a. p (f a)@.
type family ForallF (p :: k2 -> Constraint) (f :: k1 -> k2) :: Constraint
type instance ForallF p f = ForallF_ p f
class p (f (SkolemF p f)) => ForallF_ (p :: k2 -> Constraint) (f :: k1 -> k2)
instance p (f (SkolemF p f)) => ForallF_ (p :: k2 -> Constraint) (f :: k1 -> k2)

type Forall1 p = Forall p

-- | A representation of the quantified constraint @forall f a. p (t f a)@.
type family ForallT (p :: k3 -> Constraint) (t :: k1 -> k2 -> k3) :: Constraint
type instance ForallT p t = ForallT_ p t
class p (t (SkolemT1 p t) (SkolemT2 p t)) => ForallT_ (p :: k3 -> Constraint) (t :: k1 -> k2 -> k3)
instance p (t (SkolemT1 p t) (SkolemT2 p t)) => ForallT_ (p :: k3 -> Constraint) (t :: k1 -> k2 -> k3)

-- | Instantiate a quantified @'Forall' p@ constraint at type @a@.
inst :: forall p a. Forall p :- p a
inst = unsafeCoerce (Sub Dict :: Forall p :- p (Skolem p))

-- | Instantiate a quantified @'ForallF' p f@ constraint at type @a@.
instF :: forall p f a. ForallF p f :- p (f a)
instF = unsafeCoerce (Sub Dict :: ForallF p f :- p (f (SkolemF p f)))

-- | Instantiate a quantified constraint on kind @* -> *@.
-- This is now redundant since @'inst'@ became polykinded.
inst1 :: forall (p :: (* -> *) -> Constraint) (f :: * -> *). Forall p :- p f
inst1 = inst

-- | Instantiate a quantified @'ForallT' p t@ constraint at types @f@ and @a@.
instT :: forall (p :: k3 -> Constraint) (t :: k1 -> k2 -> k3) (f :: k1) (a :: k2). ForallT p t :- p (t f a)
instT = unsafeCoerce (Sub Dict :: ForallT p t :- p (t (SkolemT1 p t) (SkolemT2 p t)))
