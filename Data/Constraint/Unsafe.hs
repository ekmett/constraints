{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE GADTs #-}

module Data.Constraint.Unsafe
  ( evil
  , derive
  , underive
  -- * Sugar
  , applicative
  , alternative
  ) where

import Control.Applicative
import Control.Monad
import Control.Newtype
import Data.Constraint
import Unsafe.Coerce

evil :: a :- b
evil = unsafeCoerce refl

derive :: Newtype n o => (o -> n) -> t o :- t n
derive _ = evil

underive :: Newtype n o => (o -> n) -> t n :- t o
underive _ = evil

applicative :: forall m a. Monad m => (Applicative m => m a) -> m a
applicative m = m \\ trans (evil :: Applicative (WrappedMonad m) :- Applicative m) ins

alternative :: forall m a. MonadPlus m => (Alternative m => m a) -> m a
alternative m = m \\ trans (evil :: Alternative (WrappedMonad m) :- Alternative m) ins
