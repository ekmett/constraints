{-# LANGUAGE CPP #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveDataTypeable #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Constraint.Deferrable
-- Copyright   :  (C) 2015-2016 Edward Kmett
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  experimental
-- Portability :  non-portable
--
-- The idea for this trick comes from Dimitrios Vytiniotis.
-----------------------------------------------------------------------------

module Data.Constraint.Deferrable
  ( UnsatisfiedConstraint(..)
  , Deferrable(..)
  , defer
  , deferred
  ) where

import Control.Exception
import Control.Monad
import Data.Constraint
import Data.Proxy
import Data.Typeable (Typeable, cast)

data UnsatisfiedConstraint = UnsatisfiedConstraint String
  deriving (Typeable, Show)

instance Exception UnsatisfiedConstraint

-- | Allow an attempt at resolution of a constraint at a later time
class Deferrable (p :: Constraint) where
  -- | Resolve a 'Deferrable' constraint with observable failure.
  deferEither :: forall r proxy. proxy p -> (p => r) -> Either String r

-- | Defer a constraint for later resolution in a context where we want to upgrade failure into an error
defer :: forall p r proxy. Deferrable p => proxy p -> (p => r) -> r
defer _ r = either (throw . UnsatisfiedConstraint) id $ deferEither (Proxy :: Proxy p) r 

deferred :: forall p. Deferrable p :- p
deferred = Sub $ defer (Proxy :: Proxy p) Dict

-- We use our own type equality rather than @Data.Type.Equality@ to allow building on GHC 7.6.
data a :~: b where
  Refl :: a :~: a
    deriving Typeable

instance Deferrable () where
  deferEither _ = Right

instance (Typeable a, Typeable b) => Deferrable (a ~ b) where
  deferEither _ r = case cast (Refl :: a :~: a) :: Maybe (a :~: b) of
    Just Refl -> Right r
    Nothing -> Left "deferred type equality: type mismatch"

instance (Deferrable a, Deferrable b) => Deferrable (a, b) where
  deferEither _ r = join $ deferEither (Proxy :: Proxy a) $ deferEither (Proxy :: Proxy b) r

instance (Deferrable a, Deferrable b, Deferrable c) => Deferrable (a, b, c) where
  deferEither _ r = join $ deferEither (Proxy :: Proxy a) $ join $ deferEither (Proxy :: Proxy b) $ deferEither (Proxy :: Proxy c) r
