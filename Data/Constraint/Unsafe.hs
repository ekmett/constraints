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
  -- * Sugar
  , applicative
  , alternative
  ) where

import Control.Applicative
import Control.Monad
import Data.Constraint
import Unsafe.Coerce

evil :: a :- b
evil = unsafeCoerce refl

applicative :: forall m a. Monad m => (Applicative m => m a) -> m a
applicative m = m \\ trans (evil :: Applicative (WrappedMonad m) :- Applicative m) ins

alternative :: forall m a. MonadPlus m => (Alternative m => m a) -> m a
alternative m = m \\ trans (evil :: Alternative (WrappedMonad m) :- Alternative m) ins

