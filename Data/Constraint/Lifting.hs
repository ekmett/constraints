{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Data.Constraint.Lifting 
  ( Lifting(..)
  , Lifting2(..)
  ) where

import Data.Constraint

class Lifting p f where
  lifting :: p a :- p (f a)
  default lifting :: (Lifting2 p q, p b, f ~ q b) => p a :- p (f a)
  lifting = liftingDefault

liftingDefault :: forall p q a b. (Lifting2 p q, p a) => p b :- p (q a b)
liftingDefault = Sub $ case lifting2 :: (p a, p b) :- p (q a b) of
  Sub Dict -> Dict
  
instance Lifting Eq [] where lifting = Sub Dict
instance Lifting Ord [] where lifting = Sub Dict
instance Lifting Show [] where lifting = Sub Dict
instance Lifting Read [] where lifting = Sub Dict

instance Lifting Eq Maybe where lifting = Sub Dict
instance Lifting Ord Maybe where lifting = Sub Dict
instance Lifting Show Maybe where lifting = Sub Dict
instance Lifting Read Maybe where lifting = Sub Dict

instance Eq a => Lifting Eq (Either a)
instance Ord a => Lifting Ord (Either a)
instance Show a => Lifting Show (Either a)
instance Read a => Lifting Read (Either a)

instance Eq a => Lifting Eq ((,) a)
instance Ord a => Lifting Ord ((,) a)
instance Show a => Lifting Show ((,) a)
instance Read a => Lifting Read ((,) a)

class Lifting2 p f where
  lifting2 :: (p a, p b) :- p (f a b)

instance Lifting2 Eq Either where lifting2 = Sub Dict
instance Lifting2 Ord Either where lifting2 = Sub Dict
instance Lifting2 Show Either where lifting2 = Sub Dict
instance Lifting2 Read Either where lifting2 = Sub Dict

instance Lifting2 Eq (,) where lifting2 = Sub Dict
instance Lifting2 Ord (,) where lifting2 = Sub Dict
instance Lifting2 Show (,) where lifting2 = Sub Dict
instance Lifting2 Read (,) where lifting2 = Sub Dict
