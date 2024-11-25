{-# LANGUAGE CPP #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE GADTs #-}

-- |
-- Copyright   :  (C) 2011-2021 Edward Kmett,
--                (C) 2015 Ørjan Johansen,
--                (C) 2016 David Feuer
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  experimental
-- Portability :  non-portable
--
-- This module uses a trick to provide quantification over constraints.

module Data.Constraint.Forall
  ( Forall, inst
  , ForallF, instF
  , Forall1, inst1
  , ForallT, instT
  , ForallV, InstV (instV)
  , forall_
  ) where

import Data.Constraint
import Data.Constraint.Compose
import Unsafe.Coerce (unsafeCoerce)

class (forall a. p a) => Forall (p :: k -> Constraint)
instance (forall a. p a) => Forall (p :: k -> Constraint)

-- | Instantiate a quantified @'Forall' p@ constraint at type @a@.
inst :: forall p a. Forall p :- p a
inst = Sub Dict

data Dict1 p where
  Dict1 :: (forall a. p a) => Dict1 p

forallish :: forall p. Dict1 p -> Dict (Forall p)
forallish Dict1 = Dict

forall_ :: forall p. (forall a. Dict (p a)) -> Dict (Forall p)
forall_ d = forallish (unsafeCoerce d)

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
instT :: forall k1 k2 k3 k4 (p :: k4 -> Constraint) (t :: (k1 -> k2) -> k3 -> k4) (f :: k1 -> k2) (a :: k3). ForallT p t :- p (t f a)
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
  type ForallV' (p :: k) :: Constraint
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

