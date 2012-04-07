{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE GADTs #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Constraint
-- Copyright   :  (C) 2011-2012 Edward Kmett,
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  experimental
-- Portability :  non-portable
--
----------------------------------------------------------------------------


module Data.Constraint
  (
  -- * Constraints
    Constraint
  -- * Dictionary
  , Dict(Dict)
  -- * Entailment
  , (:-)(Sub)
  , (\\)
  , weaken1, weaken2, contract
  , (&&&), (***)
  , trans, refl
  , top
  -- * Reflection
  , Class(..)
  , (:=>)(..)
  ) where

import Control.Monad
import Control.Applicative
import Data.Monoid
import Data.Complex
import Data.Ratio
import GHC.Prim (Constraint)

-- | Capture a dictionary for a given constraint
data Dict :: Constraint -> * where
  Dict :: a => Dict a

deriving instance Eq (Dict a)
deriving instance Ord (Dict a)
deriving instance Show (Dict a)

infixr 9 :-
newtype a :- b = Sub (a => Dict b)

instance Eq (a :- b) where
  _ == _ = True

instance Ord (a :- b) where
  compare _ _ = EQ

instance Show (a :- b) where
  showsPrec d _ = showParen (d > 10) $ showString "Sub Dict"

infixl 1 \\ -- required comment

-- | Given that @a :- b@, derive something that needs a context @b@, using the context @a@
(\\) :: a => (b => r) -> (a :- b) -> r
r \\ Sub Dict = r

-- | due to the hack for the kind of (,) in the current version of GHC we can't actually
-- make instances for (,) :: Constraint -> Constraint -> Constraint
(***) :: (a :- b) -> (c :- d) -> (a, c) :- (b, d)
f *** g = Sub $ Dict \\ f \\ g

-- | Weakening a constraint product
weaken1 :: (a, b) :- a
weaken1 = Sub Dict

-- | Weakening a constraint product
weaken2 :: (a, b) :- b
weaken2 = Sub Dict

-- | Contracting a constraint / diagonal morphism
contract :: a :- (a, a)
contract = Sub Dict

-- | Constraint product
--
-- > trans weaken1 (f &&& g) = f
-- > trans weaken2 (f &&& g) = g
(&&&) :: (a :- b) -> (a :- c) -> a :- (b, c)
f &&& g = Sub $ Dict \\ f \\ g

--    ?
--   / \
-- (#)  ??  ???
--     /  \ / \
--    #    *  Constraint

-- | Transitivity of entailment
--
-- If we view '(:-)' as a Constraint-indexed category, then this is '(.)'
trans :: (b :- c) -> (a :- b) -> a :- c
trans f g = Sub $ Dict \\ f \\ g

-- | Reflexivity of entailment
-- 
-- If we view '(:-)' as a Constraint-indexed category, then this is 'id'
refl :: a :- a
refl = Sub Dict

-- | Every constraint implies truth
--
-- These are the terminal arrows of the category, and () is the terminal object.
top :: a :- ()
top = Sub Dict

-- | Reify the relationship between a class and its superclass constraints as a class
class Class b h | h -> b where
  cls :: h :- b

infixr 9 :=>
-- | Reify the relationship between an instance head and its body as a class
class b :=> h | h -> b where
  ins :: b :- h

instance Class () (Class b a) where cls = Sub Dict
instance Class () (b :=> a) where cls = Sub Dict

instance Class b a => () :=> Class b a where ins = Sub Dict
instance (b :=> a) => () :=> b :=> a where ins = Sub Dict

instance Class () () where cls = Sub Dict
instance () :=> () where ins = Sub Dict

-- Local, Prelude, Applicative, C.M.I and Data.Monoid instances

-- Eq
instance Class () (Eq a) where cls = Sub Dict
instance () :=> Eq () where ins = Sub Dict
instance () :=> Eq Int where ins = Sub Dict
instance () :=> Eq Bool where ins = Sub Dict
instance () :=> Eq Integer where ins = Sub Dict
instance () :=> Eq Float where ins = Sub Dict
instance () :=> Eq Double where ins = Sub Dict
instance Eq a :=> Eq [a] where ins = Sub Dict
instance Eq a :=> Eq (Maybe a) where ins = Sub Dict
instance Eq a :=> Eq (Complex a) where ins = Sub Dict
instance Eq a :=> Eq (Ratio a) where ins = Sub Dict
instance (Eq a, Eq b) :=> Eq (a, b) where ins = Sub Dict
instance (Eq a, Eq b) :=> Eq (Either a b) where ins = Sub Dict
instance () :=> Eq (Dict a) where ins = Sub Dict
instance () :=> Eq (a :- b) where ins = Sub Dict

-- Ord
instance Class (Eq a) (Ord a) where cls = Sub Dict
instance () :=> Ord () where ins = Sub Dict
instance () :=> Ord Bool where ins = Sub Dict
instance () :=> Ord Int where ins = Sub Dict
instance ():=> Ord Integer where ins = Sub Dict
instance () :=> Ord Float where ins = Sub Dict
instance ():=> Ord Double where ins = Sub Dict
instance () :=> Ord Char where ins = Sub Dict
instance Ord a :=> Ord (Maybe a) where ins = Sub Dict
instance Ord a :=> Ord [a] where ins = Sub Dict
instance (Ord a, Ord b) :=> Ord (a, b) where ins = Sub Dict
instance (Ord a, Ord b) :=> Ord (Either a b) where ins = Sub Dict
instance Integral a :=> Ord (Ratio a) where ins = Sub Dict
instance () :=> Ord (Dict a) where ins = Sub Dict
instance () :=> Ord (a :- b) where ins = Sub Dict

instance Class () (Show a) where cls = Sub Dict
instance () :=> Show () where ins = Sub Dict
instance () :=> Show Bool where ins = Sub Dict
instance () :=> Show Ordering where ins = Sub Dict
instance () :=> Show Char where ins = Sub Dict
instance Show a :=> Show (Complex a) where ins = Sub Dict
instance Show a :=> Show [a] where ins = Sub Dict
instance Show a :=> Show (Maybe a) where ins = Sub Dict
instance (Show a, Show b) :=> Show (a, b) where ins = Sub Dict
instance (Show a, Show b) :=> Show (Either a b) where ins = Sub Dict
instance (Integral a, Show a) :=> Show (Ratio a) where ins = Sub Dict
instance () :=> Show (Dict a) where ins = Sub Dict
instance () :=> Show (a :- b) where ins = Sub Dict

instance Class () (Read a) where cls = Sub Dict
instance () :=> Read () where ins = Sub Dict
instance () :=> Read Bool where ins = Sub Dict
instance () :=> Read Ordering where ins = Sub Dict
instance () :=> Read Char where ins = Sub Dict
instance Read a :=> Read (Complex a) where ins = Sub Dict
instance Read a :=> Read [a] where ins = Sub Dict
instance Read a :=> Read (Maybe a) where ins = Sub Dict
instance (Read a, Read b) :=> Read (a, b) where ins = Sub Dict
instance (Read a, Read b) :=> Read (Either a b) where ins = Sub Dict
instance (Integral a, Read a) :=> Read (Ratio a) where ins = Sub Dict

instance Class () (Enum a) where cls = Sub Dict
instance () :=> Enum () where ins = Sub Dict
instance () :=> Enum Bool where ins = Sub Dict
instance () :=> Enum Ordering where ins = Sub Dict
instance () :=> Enum Char where ins = Sub Dict
instance () :=> Enum Int where ins = Sub Dict
instance () :=> Enum Integer where ins = Sub Dict
instance () :=> Enum Float where ins = Sub Dict
instance () :=> Enum Double where ins = Sub Dict
instance Integral a :=> Enum (Ratio a) where ins = Sub Dict

instance Class () (Bounded a) where cls = Sub Dict
instance () :=> Bounded () where ins = Sub Dict
instance () :=> Bounded Ordering where ins = Sub Dict
instance () :=> Bounded Bool where ins = Sub Dict
instance () :=> Bounded Int where ins = Sub Dict
instance () :=> Bounded Char where ins = Sub Dict
instance (Bounded a, Bounded b) :=> Bounded (a,b) where ins = Sub Dict

instance Class () (Num a) where cls = Sub Dict
instance () :=> Num Int where ins = Sub Dict
instance () :=> Num Integer where ins = Sub Dict
instance () :=> Num Float where ins = Sub Dict
instance () :=> Num Double where ins = Sub Dict
instance RealFloat a :=> Num (Complex a) where ins = Sub Dict
instance Integral a :=> Num (Ratio a) where ins = Sub Dict

instance Class (Num a, Ord a) (Real a) where cls = Sub Dict
instance () :=> Real Int where ins = Sub Dict
instance () :=> Real Integer where ins = Sub Dict
instance () :=> Real Float where ins = Sub Dict
instance () :=> Real Double where ins = Sub Dict
instance Integral a :=> Real (Ratio a) where ins = Sub Dict

instance Class (Real a, Enum a) (Integral a) where cls = Sub Dict
instance () :=> Integral Int where ins = Sub Dict
instance () :=> Integral Integer where ins = Sub Dict

instance Class (Num a) (Fractional a) where cls = Sub Dict
instance () :=> Fractional Float where ins = Sub Dict
instance () :=> Fractional Double where ins = Sub Dict
instance RealFloat a :=> Fractional (Complex a) where ins = Sub Dict
instance Integral a :=> Fractional (Ratio a) where ins = Sub Dict

instance Class (Fractional a) (Floating a) where cls = Sub Dict
instance () :=> Floating Float where ins = Sub Dict
instance () :=> Floating Double where ins = Sub Dict
instance RealFloat a :=> Floating (Complex a) where ins = Sub Dict

instance Class (Real a, Fractional a) (RealFrac a) where cls = Sub Dict
instance () :=> RealFrac Float where ins = Sub Dict
instance () :=> RealFrac Double where ins = Sub Dict
instance Integral a :=> RealFrac (Ratio a) where ins = Sub Dict

instance Class (RealFrac a, Floating a) (RealFloat a) where cls = Sub Dict
instance () :=> RealFloat Float where ins = Sub Dict
instance () :=> RealFloat Double where ins = Sub Dict

instance Class () (Monoid a) where cls = Sub Dict
instance () :=> Monoid () where ins = Sub Dict
instance () :=> Monoid Ordering where ins = Sub Dict
instance () :=> Monoid [a] where ins = Sub Dict
instance Monoid a :=> Monoid (Maybe a) where ins = Sub Dict
instance (Monoid a, Monoid b) :=> Monoid (a, b) where ins = Sub Dict

instance Class () (Functor f) where cls = Sub Dict
instance () :=> Functor [] where ins = Sub Dict
instance () :=> Functor Maybe where ins = Sub Dict
instance () :=> Functor (Either a) where ins = Sub Dict
instance () :=> Functor ((->) a) where ins = Sub Dict
instance () :=> Functor ((,) a) where ins = Sub Dict
instance () :=> Functor IO where ins = Sub Dict
instance Monad m :=> Functor (WrappedMonad m) where ins = Sub Dict

instance Class (Functor f) (Applicative f) where cls = Sub Dict
instance () :=> Applicative [] where ins = Sub Dict
instance () :=> Applicative Maybe where ins = Sub Dict
instance () :=> Applicative (Either a) where ins = Sub Dict
instance () :=> Applicative ((->)a) where ins = Sub Dict
instance () :=> Applicative IO where ins = Sub Dict
instance Monoid a :=> Applicative ((,)a) where ins = Sub Dict
instance Monad m :=> Applicative (WrappedMonad m) where ins = Sub Dict

instance Class (Applicative f) (Alternative f) where cls = Sub Dict
instance () :=> Alternative [] where ins = Sub Dict
instance () :=> Alternative Maybe where ins = Sub Dict
instance MonadPlus m :=> Alternative (WrappedMonad m) where ins = Sub Dict

instance Class () (Monad f) where cls = Sub Dict
instance () :=> Monad [] where ins = Sub Dict
instance () :=> Monad ((->) a) where ins = Sub Dict
instance () :=> Monad (Either a) where ins = Sub Dict
instance () :=> Monad IO where ins = Sub Dict

instance Class (Monad f) (MonadPlus f) where cls = Sub Dict
instance () :=> MonadPlus [] where ins = Sub Dict
instance () :=> MonadPlus Maybe where ins = Sub Dict

-- UndecidableInstances
instance a :=> Enum (Dict a) where ins = Sub Dict
instance a => Enum (Dict a) where
  toEnum _ = Dict
  fromEnum Dict = 0

instance a :=> Bounded (Dict a) where ins = Sub Dict
instance a => Bounded (Dict a) where
  minBound = Dict
  maxBound = Dict

instance a :=> Read (Dict a) where ins = Sub Dict
deriving instance a => Read (Dict a)

instance a :=> Monoid (Dict a) where ins = Sub Dict
instance a => Monoid (Dict a) where
  mappend Dict Dict = Dict
  mempty = Dict
