{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE Trustworthy #-}

module Data.Constraint.Forall
  ( Forall, inst
  , Forall1, inst1
  ) where

import Data.Constraint
import Data.Constraint.Unsafe

-- skolem variables, do not export!
data A
data B
type Forall (p :: * -> Constraint) = (p A, p B)

data F a
data M a
type Forall1 (p :: (* -> *) -> Constraint) = (p F, p M)

inst :: forall p a. Forall p :- p a
inst = trans (evil :: p A :- p a) weaken1

inst1 :: forall (p :: (* -> *) -> Constraint) (f :: * -> *). Forall1 p :- p f
inst1 = trans (evil :: p F :- p f) weaken1
