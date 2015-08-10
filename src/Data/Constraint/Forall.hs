{-# LANGUAGE CPP #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
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
  ( Forall(..), inst, forall
  , ForallT(..), instT, forallT
  ) where

import Data.Constraint
import Unsafe.Coerce

class Forall p where
  instantiate :: Dict (p a)

inst :: Forall p :- p a
inst = Sub instantiate

newtype Magic p r = Magic (Forall p => Dict (Forall p))

forall :: (forall a. Dict (p a)) -> Dict (Forall p)
forall p = unsafeCoerce (Magic Dict) p

class ForallT p t where
  instantiateT :: Dict (p (t f a))

instT :: ForallT p t :- p (t f a)
instT = Sub instantiateT

newtype MagicT p t r = MagicT (ForallT p t => Dict (ForallT p t))

forallT :: (forall f a. Dict (p (t f a))) -> Dict (ForallT p t)
forallT p = unsafeCoerce (MagicT Dict) p
