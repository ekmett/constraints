{-# LANGUAGE CPP #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE PolyKinds #-}
#if __GLASGOW_HASKELL__ >= 800
{-# LANGUAGE UndecidableSuperClasses #-}
#endif
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Constraint.Forall
-- Copyright   :  (C) 2011-2015 Edward Kmett,
--                (C) 2015 Ørjan Johansen,
--                (C) 2016 David Feuer
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
  , ForallV, InstV (instV)
  , forall
  ) where

import Data.Constraint
import Unsafe.Coerce (unsafeCoerce)

{- The basic trick of this module is to use "skolem" types as test candidates
 - for whether a class predicate holds, and if so assume that it holds for all
 - types, unsafely coercing the typeclass dictionary.
 -
 - The particular technique used to implement 'Forall' appears to have been
 - discovered first by Nicolas Frisby and is
 - <https://csks.wordpress.com/2012/10/22/safe-polykinded-universally-quantified-constraints-part-3-of-3/ discussed in some detail>
 - on his blog.
 -
 - However, his discovery did not directly affect the development of this
 - module.
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

-- The `Skolem` type family represents skolem variables; do not export!
-- If GHC supports it, these might be made closed with no instances.

type family Skolem (p :: k -> Constraint) :: k

-- The outer `Forall` type family prevents GHC from giving a spurious
-- superclass cycle error.
-- The inner `Forall_` class prevents the skolem from leaking to the user,
-- which would be disastrous.

-- | A representation of the quantified constraint @forall a. p a@.
type family Forall (p :: k -> Constraint) :: Constraint
type instance Forall p = Forall_ p
class p (Skolem p) => Forall_ (p :: k -> Constraint)
instance p (Skolem p) => Forall_ (p :: k -> Constraint)

-- | Instantiate a quantified @'Forall' p@ constraint at type @a@.
inst :: forall p a. Forall p :- p a
inst = unsafeCoerce (Sub Dict :: Forall p :- p (Skolem p))

-- | Composition for constraints.
class p (f a) => ComposeC (p :: k2 -> Constraint) (f :: k1 -> k2) (a :: k1)
instance p (f a) => ComposeC p f a

-- | A representation of the quantified constraint @forall a. p (f a)@.
class Forall (ComposeC p f) => ForallF (p :: k2 -> Constraint) (f :: k1 -> k2)
instance Forall (ComposeC p f) => ForallF p f

-- | Instantiate a quantified @'ForallF' p f@ constraint at type @a@.
instF :: forall p f a . ForallF p f :- p (f a)
instF = Sub $
  case inst :: Forall (ComposeC p f) :- ComposeC p f a of
    Sub Dict -> Dict

-- Classes building up to ForallT
class p (t a b) => R (p :: k3 -> Constraint) (t :: k1 -> k2 -> k3) (a :: k1) (b :: k2)
instance p (t a b) => R p t a b
class Forall (R p t a) => Q (p :: k3 -> Constraint) (t :: k1 -> k2 -> k3) (a :: k1)
instance Forall (R p t a) => Q p t a

-- | A representation of the quantified constraint @forall f a. p (t f a)@.
class Forall (Q p t) => ForallT (p :: k4 -> Constraint) (t :: (k1 -> k2) -> k3 -> k4)
instance Forall (Q p t) => ForallT p t

-- | Instantiate a quantified @'ForallT' p t@ constraint at types @f@ and @a@.
instT :: forall (p :: k4 -> Constraint) (t :: (k1 -> k2) -> k3 -> k4) (f :: k1 -> k2) (a :: k3). ForallT p t :- p (t f a)
instT = Sub $
  case inst :: Forall (Q p t) :- Q p t f of { Sub Dict ->
  case inst :: Forall (R p t f) :- R p t f a of
    Sub Dict -> Dict }

type Forall1 p = Forall p
-- | Instantiate a quantified constraint on kind @* -> *@.
-- This is now redundant since @'inst'@ became polykinded.
inst1 :: forall (p :: (* -> *) -> Constraint) (f :: * -> *). Forall p :- p f
inst1 = inst

-- | A representation of the quantified constraint
-- @forall a1 a2 ... an . p a1 a2 ... an@, supporting a variable number of
-- parameters.
type family ForallV :: k -> Constraint
type instance ForallV = ForallV_

class ForallV' p => ForallV_ (p :: k)
instance ForallV' p => ForallV_ p

-- | Instantiate a quantified @'ForallV' p@ constraint as @c@, where
-- @c ~ p a1 a2 ... an@.
class InstV (p :: k) c | k c -> p where
    type family ForallV' (p :: k) :: Constraint
    instV :: ForallV p :- c

instance p ~ c => InstV (p :: Constraint) c where
    type ForallV' (p :: Constraint) = p
    instV = Sub Dict

-- Treating 1 argument specially rather than recursing as a bit of (premature?)
-- optimization
instance p a ~ c => InstV (p :: k -> Constraint) c where
    type ForallV' (p :: k -> Constraint) = Forall p
    instV = Sub $ case inst :: Forall p :- c of
        Sub Dict -> Dict

instance InstV (p a) c => InstV (p :: k1 -> k2 -> k3) c where
    type ForallV' (p :: k1 -> k2 -> k3) = ForallF ForallV p
    instV = Sub $ case instF :: ForallF ForallV p :- ForallV (p a) of
        Sub Dict -> case instV :: ForallV (p a) :- c of
            Sub Dict -> Dict

forall :: forall p. (forall a. Dict (p a)) -> Dict (Forall p)
forall d = case d :: Dict (p (Skolem p)) of Dict -> Dict
