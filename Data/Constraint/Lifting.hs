{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
module Data.Constraint.Lifting 
  ( Lifting(..)
  , Lifting2(..)
  ) where

import Control.Applicative
import Control.DeepSeq
import Data.Binary
import Data.Constraint
import Data.Foldable
import Data.Functor.Compose as Functor
import Data.Functor.Product as Functor
import Data.Functor.Sum as Functor
import Data.Hashable
import Data.Monoid
import Data.Traversable

class Lifting p f where
  lifting :: p a :- p (f a)
  default lifting :: (Lifting2 p q, p b, f ~ q b) => p a :- p (f a)
  lifting = liftingDefault

liftingDefault :: forall p q a b. (Lifting2 p q, p a) => p b :- p (q a b)
liftingDefault = Sub $ case lifting2 :: (p a, p b) :- p (q a b) of
  Sub Dict -> Dict

{-
instance Lifting Monad (StateT s) where lifting = Sub Dict
instance Lifting Monad (ReaderT e) where lifting = Sub Dict
instance Lifting Monad (WriterT w) where lifting = Sub Dict
-}

instance Lifting Eq [] where lifting = Sub Dict
instance Lifting Ord [] where lifting = Sub Dict
instance Lifting Show [] where lifting = Sub Dict
instance Lifting Read [] where lifting = Sub Dict
instance Lifting Hashable [] where lifting = Sub Dict
instance Lifting Binary [] where lifting = Sub Dict
instance Lifting NFData [] where lifting = Sub Dict

instance Lifting Eq Maybe where lifting = Sub Dict
instance Lifting Ord Maybe where lifting = Sub Dict
instance Lifting Show Maybe where lifting = Sub Dict
instance Lifting Read Maybe where lifting = Sub Dict
instance Lifting Hashable Maybe where lifting = Sub Dict
instance Lifting Binary Maybe where lifting = Sub Dict
instance Lifting NFData Maybe where lifting = Sub Dict

instance Eq a => Lifting Eq (Either a)
instance Ord a => Lifting Ord (Either a)
instance Show a => Lifting Show (Either a)
instance Read a => Lifting Read (Either a)
instance Hashable a => Lifting Hashable (Either a)
instance Binary a => Lifting Binary (Either a)
instance NFData a => Lifting NFData (Either a)

instance Eq a => Lifting Eq ((,) a)
instance Ord a => Lifting Ord ((,) a)
instance Show a => Lifting Show ((,) a)
instance Read a => Lifting Read ((,) a)
instance Hashable a => Lifting Hashable ((,) a)
instance Binary a => Lifting Binary ((,) a)
instance NFData a => Lifting NFData ((,) a)
instance Monoid a => Lifting Monoid ((,) a)

instance Functor f => Lifting Functor (Compose f)
instance Applicative f => Lifting Applicative (Compose f)

instance Functor f => Lifting Functor (Functor.Product f)
instance Functor f => Lifting Functor (Functor.Sum f)

class Lifting2 p f where
  lifting2 :: (p a, p b) :- p (f a b)

instance Lifting2 Eq Either where lifting2 = Sub Dict
instance Lifting2 Ord Either where lifting2 = Sub Dict
instance Lifting2 Show Either where lifting2 = Sub Dict
instance Lifting2 Read Either where lifting2 = Sub Dict
instance Lifting2 Hashable Either where lifting2 = Sub Dict
instance Lifting2 Binary Either where lifting2 = Sub Dict
instance Lifting2 NFData Either where lifting2 = Sub Dict

instance Lifting2 Eq (,) where lifting2 = Sub Dict
instance Lifting2 Ord (,) where lifting2 = Sub Dict
instance Lifting2 Show (,) where lifting2 = Sub Dict
instance Lifting2 Read (,) where lifting2 = Sub Dict
instance Lifting2 Hashable (,) where lifting2 = Sub Dict
instance Lifting2 Binary (,) where lifting2 = Sub Dict
instance Lifting2 NFData (,) where lifting2 = Sub Dict
instance Lifting2 Monoid (,) where lifting2 = Sub Dict

instance Lifting2 Functor Compose where lifting2 = Sub Dict
instance Lifting2 Foldable Compose where lifting2 = Sub Dict
instance Lifting2 Traversable Compose where lifting2 = Sub Dict
instance Lifting2 Applicative Compose where lifting2 = Sub Dict

instance Lifting2 Functor Functor.Product where lifting2 = Sub Dict
instance Lifting2 Foldable Functor.Product where lifting2 = Sub Dict
instance Lifting2 Traversable Functor.Product where lifting2 = Sub Dict

instance Lifting2 Functor Functor.Sum where lifting2 = Sub Dict
instance Lifting2 Foldable Functor.Sum where lifting2 = Sub Dict
instance Lifting2 Traversable Functor.Sum where lifting2 = Sub Dict
