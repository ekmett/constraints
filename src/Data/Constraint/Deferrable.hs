{-# LANGUAGE CPP #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE PolyKinds #-}

#if __GLASGOW_HASKELL__ >= 800
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeInType #-}
#endif

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
#if __GLASGOW_HASKELL__ >= 800
  , defer_
  , deferEither_
  , (:~~:)(HRefl)
#endif
  , (:~:)(Refl)
  ) where

import Control.Exception
import Control.Monad
import Data.Constraint
import Data.Proxy
import Data.Typeable (Typeable, cast, typeRep)
import Data.Type.Equality ((:~:)(Refl))

#if __GLASGOW_HASKELL__ >= 800
import GHC.Types (type (~~))
#endif

data UnsatisfiedConstraint = UnsatisfiedConstraint String
  deriving (Typeable, Show)

instance Exception UnsatisfiedConstraint

-- | Allow an attempt at resolution of a constraint at a later time
class Deferrable p where
  -- | Resolve a 'Deferrable' constraint with observable failure.
  deferEither :: proxy p -> (p => r) -> Either String r

-- | Defer a constraint for later resolution in a context where we want to upgrade failure into an error
defer :: forall p r proxy. Deferrable p => proxy p -> (p => r) -> r
defer _ r = either (throw . UnsatisfiedConstraint) id $ deferEither (Proxy :: Proxy p) r

deferred :: forall p. Deferrable p :- p
deferred = Sub $ defer (Proxy :: Proxy p) Dict

#if __GLASGOW_HASKELL__ >= 800
-- | A version of 'defer' that uses visible type application in place of a 'Proxy'.
--
-- Only available on GHC 8.0 or later.
defer_ :: forall p r. Deferrable p => (p => r) -> r
defer_ r = defer @p Proxy r

-- | A version of 'deferEither' that uses visible type application in place of a 'Proxy'.
--
-- Only available on GHC 8.0 or later.
deferEither_ :: forall p r. Deferrable p => (p => r) -> Either String r
deferEither_ r = deferEither @p Proxy r
#endif

#if __GLASGOW_HASKELL__ >= 800
-- | Kind heterogeneous propositional equality. Like '(:~:)', @a :~~: b@ is
-- inhabited by a terminating value if and only if @a@ is the same type as @b@.
--
-- Only available on GHC 8.0 or later.
data (a :: i) :~~: (b :: j) where
  HRefl :: a :~~: a
    deriving Typeable
#endif

showTypeRep :: Typeable t => Proxy t -> String
showTypeRep = show . typeRep

instance Deferrable () where
  deferEither _ r = Right r

-- | Deferrable homogeneous equality constraints.
--
-- Note that due to a GHC bug (https://ghc.haskell.org/trac/ghc/ticket/10343),
-- using this instance on GHC 7.10 will only work with @*@-kinded types.
#if __GLASGOW_HASKELL__ >= 800
instance (Typeable k, Typeable (a :: k), Typeable b) => Deferrable (a ~ b) where
#elif __GLASGOW_HASKELL__ == 710
instance (Typeable a, Typeable b) => Deferrable ((a :: *) ~ (b :: *)) where
#else
instance (Typeable a, Typeable b) => Deferrable (a ~ b) where
#endif
  deferEither _ r = case cast (Refl :: a :~: a) :: Maybe (a :~: b) of
    Just Refl -> Right r
    Nothing   -> Left $
      "deferred type equality: type mismatch between `" ++ showTypeRep (Proxy :: Proxy a) ++ "’ and `"  ++ showTypeRep (Proxy :: Proxy b) ++ "'"

#if __GLASGOW_HASKELL__ >= 800
-- | Deferrable heterogenous equality constraints.
--
-- Only available on GHC 8.0 or later.
instance (Typeable i, Typeable j, Typeable (a :: i), Typeable (b :: j)) => Deferrable (a ~~ b) where
  deferEither _ r = case cast (HRefl :: a :~~: a) :: Maybe (a :~~: b) of
    Just HRefl -> Right r
    Nothing   -> Left $
      "deferred type equality: type mismatch between `" ++ showTypeRep (Proxy :: Proxy a) ++ "’ and `"  ++ showTypeRep (Proxy :: Proxy b) ++ "'"
#endif

instance (Deferrable a, Deferrable b) => Deferrable (a, b) where
  deferEither _ r = join $ deferEither (Proxy :: Proxy a) $ deferEither (Proxy :: Proxy b) r

instance (Deferrable a, Deferrable b, Deferrable c) => Deferrable (a, b, c) where
  deferEither _ r = join $ deferEither (Proxy :: Proxy a) $ join $ deferEither (Proxy :: Proxy b) $ deferEither (Proxy :: Proxy c) r
