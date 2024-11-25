{-# LANGUAGE CPP #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE PolyKinds #-}
#if __GLASGOW_HASKELL__ >= 800
{-# LANGUAGE UndecidableSuperClasses #-}
#endif

module Data.Constraint.Compose
  ( ComposeC
  ) where

import Data.Constraint

-- | Composition for constraints.
class p (f a) => ComposeC (p :: k2 -> Constraint) (f :: k1 -> k2) (a :: k1)
instance p (f a) => ComposeC p f a
