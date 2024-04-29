{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

-- |
-- Copyright   :  (C) 2015-2021 Edward Kmett
-- License     :  BSD-style (see the file LICENSE)
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  experimental
-- Portability :  non-portable
--
-- The idea for this trick comes from Dimitrios Vytiniotis.

module Data.Constraint.Deferrable
  ( UnsatisfiedConstraint(..)
  , Deferrable(..)
  , defer
  , deferred
  , (:~~:)(HRefl)
  , (:~:)(Refl)
  ) where

import Control.Exception
import Control.Monad
import Data.Constraint
import Data.Proxy
import Data.Typeable (Typeable, cast, typeRep)
import Data.Type.Equality ((:~:)(Refl))

import GHC.Types (type (~~))
import Data.Type.Equality ((:~~:)(HRefl))

newtype UnsatisfiedConstraint = UnsatisfiedConstraint String
  deriving (Typeable, Show)

instance Exception UnsatisfiedConstraint

-- | Allow an attempt at resolution of a constraint at a later time
class Deferrable p where
  -- | Resolve a 'Deferrable' constraint with observable failure.
  deferEither :: (p => r) -> Either String r

deferred :: forall p. Deferrable p :- p
deferred = Sub $ defer @p Dict

defer :: forall p r. Deferrable p => (p => r) -> r
defer r = either (throw . UnsatisfiedConstraint) id $ deferEither @p r

showTypeRep :: forall t. Typeable t => String
showTypeRep = show $ typeRep (Proxy @t)

instance Deferrable () where
  deferEither r = Right r

-- | Deferrable homogeneous equality constraints.
--
-- Note that due to a GHC bug (https://ghc.haskell.org/trac/ghc/ticket/10343),
-- using this instance on GHC 7.10 will only work with @*@-kinded types.
instance (Typeable k, Typeable (a :: k), Typeable b) => Deferrable (a ~ b) where
  deferEither r = case cast (Refl :: a :~: a) :: Maybe (a :~: b) of
    Just Refl -> Right r
    Nothing   -> Left $
      "deferred type equality: type mismatch between `" ++ showTypeRep @a ++ "’ and `"  ++ showTypeRep @b ++ "'"

-- | Deferrable heterogenous equality constraints.
--
-- Only available on GHC 8.0 or later.
instance (Typeable i, Typeable j, Typeable (a :: i), Typeable (b :: j)) => Deferrable (a ~~ b) where
  deferEither r = case cast (HRefl :: a :~~: a) :: Maybe (a :~~: b) of
    Just HRefl -> Right r
    Nothing   -> Left $
      "deferred type equality: type mismatch between `" ++ showTypeRep @a ++ "’ and `"  ++ showTypeRep @b ++ "'"

instance (Deferrable a, Deferrable b) => Deferrable (a, b) where
  deferEither r = join $ deferEither @a $ deferEither @b r

instance (Deferrable a, Deferrable b, Deferrable c) => Deferrable (a, b, c) where
  deferEither r = join $ deferEither @a $ join $ deferEither @b $ deferEither @c r
