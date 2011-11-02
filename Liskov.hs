{-# LANGUAGE ConstraintKinds, KindSignatures, TypeOperators, RankNTypes, GADTs, ScopedTypeVariables, FunctionalDependencies, TypeFamilies, FlexibleInstances, FlexibleContexts, DefaultSignatures, UndecidableInstances #-}

module Liskov where

import Prelude hiding (sum)
import Control.Monad.Instances
import Data.Monoid

data Dict :: Constraint -> * where
  Dict :: a => Dict a

runDict :: Dict a -> (a => r) -> r
runDict Dict r = r

data (:<=) :: Constraint -> Constraint -> * where
  Sub :: (a => Dict b) -> a :<= b

infixl 5 //
(//) :: a => (b => r) -> (a :<= b) -> r
r // Sub Dict = r

runSub :: a => (a :<= b) -> (b => r) -> r
runSub (Sub Dict) r = r

fstS :: (a,b) :<= a
fstS = Sub Dict

sndS :: (a,b) :<= b
sndS = Sub Dict

-- terminal arrow
type Top = (() :: Constraint)
top :: a :<= Top
top = Sub Dict

-- class Cat (k :: x -> x -> *) where
class Cat (k :: Constraint -> Constraint -> *) where
  o  :: k b c -> k a b -> k a c
  ic :: k a a

instance Cat (:<=) where
  f `o` g = Sub (Dict // f // g)
  ic = Sub Dict

class Class (b :: Constraint) (h :: Constraint) | h -> b where
  super :: h :<= b

instance Class ()     ()           where super = Sub Dict
instance Class (Eq a) (Ord a)      where super = Sub Dict
instance Class ()     (Eq a)       where super = Sub Dict
instance Class ()     (Enum a)     where super = Sub Dict
instance Class ()     (Bounded a)  where super = Sub Dict
instance Class ()     (Class () h) where super = Sub Dict
instance Class ()     (Num a)      where super = Sub Dict -- NB: Eq, and Show are no longer superclasses
instance Class ()     (Functor f)  where super = Sub Dict
instance Class ()     (Monoid a)   where super = Sub Dict


class Instance (h :: Constraint) where
  type Context h :: Constraint
  type Context h = ()

  inst  :: Context h :<= h
--  default inst :: Tautology h => () :<= h
--  inst = taut

-- not implementable using the current constraint kind hack, we need a proper polymorphic kind for (,)
-- class BifunctorS (f :: Constraint -> Constraint -> Constraint) where
--   bimapS :: (a :<= b) -> (c :<= d) -> f a c :<= f b d

(***) :: (a :<= b) -> (c :<= d) -> (a, c) :<= (b, d)
f *** g = Sub (Dict // f // g)

lub :: (a :<= c) -> (b :<= c) -> (a, b) :<= c
lub f g = Sub (Dict // f // g)

(&&&) :: (a :<= b) -> (a :<= c) -> a :<= (b,c)
f &&& g = Sub (Dict // f // g)

-- instance Tautology () where taut = Sub Dict
instance Instance () where inst = Sub Dict
instance Instance (Instance ()) where inst = Sub Dict

instance (Instance a, Instance b) => Instance (a, b) where
  type Context (a, b) = (Context a, Context b)
  inst = inst *** inst
instance (Instance (Instance a), Instance (Instance b)) => Instance (Instance (a, b)) where
  type Context (Instance (a, b)) = (Context (Instance a), Context (Instance b))
  inst = Sub (Dict // ((inst :: Context (Instance a) :<= Instance a) *** (inst :: Context (Instance b) :<= Instance b)))

instance Instance (Class () (Class () h)) where inst = Sub Dict
instance Instance (Eq ()) where inst = Sub Dict
instance Instance (Instance (Eq ())) where inst = Sub Dict
instance Instance (Eq Int) where inst = Sub Dict
instance Instance (Instance (Eq Int)) where inst = Sub Dict
instance Instance (Eq [a]) where
  type Context (Eq [a]) = Eq a
  inst = Sub Dict
instance Instance (Instance (Eq [a])) where inst = Sub Dict
instance Instance (Eq (a,b)) where
  type Context (Eq (a,b)) = (Eq a, Eq b)
  inst = Sub Dict
instance Instance (Instance (Eq (a,b))) where inst = Sub Dict

instance Instance (Ord ())    where inst = Sub Dict
instance Instance (Instance (Ord ())) where inst = Sub Dict
instance Instance (Ord Int)   where inst = Sub Dict
instance Instance (Instance (Ord Int)) where inst = Sub Dict
instance Instance (Ord [a])   where
  type Context (Ord [a]) = Ord a
  inst = Sub Dict
instance Instance (Instance (Ord [a])) where inst = Sub Dict
instance Instance (Ord (a,b)) where 
  type Context (Ord (a,b)) = (Ord a, Ord b)
  inst = Sub Dict
instance Instance (Instance (Ord (a,b))) where inst = Sub Dict

instance Instance (Functor []) where inst = Sub Dict
instance Instance (Instance (Functor [])) where inst = Sub Dict

instance Instance (Functor ((->) a)) where inst = Sub Dict
instance Instance (Instance (Functor ((->)a))) where inst = Sub Dict

instance Instance (Functor ((,) a)) where
  type Context (Functor ((,) a)) = Monoid a
  inst = Sub Dict
instance Instance (Instance (Functor ((,) a))) where inst = Sub Dict

-- With a current GHC HEAD we should be able to ditch UndecidableInstances
instance Instance (Instance a) => Instance (Instance (Instance a)) where
  type Context (Instance (Instance a)) = Instance a
  inst = Sub Dict

data (:~) :: Constraint -> Constraint -> * where
  Equiv :: (a => Dict b) -> (b => Dict a) -> a :~ b

hither :: (a :~ b) -> a :<= b
hither (Equiv a _) = Sub a

yon :: (a :~ b) -> b :<= a
yon (Equiv _ b) = Sub b

swapE :: (a,b) :~ (b,a)
swapE = Equiv Dict Dict

smashE :: (a :<= b) -> (b :<= a) -> a :~ b
smashE (Sub a) (Sub b) = Equiv a b

instance Cat (:~) where
  f `o` g = Equiv (Dict // hither f // hither g) (Dict // yon g // yon f)
  ic = Equiv Dict Dict

class EquivariantCS (f :: Constraint -> *) where
  invCS :: (a :~ b) -> f a -> f b
  default invCS :: CovariantCS f => (a :~ b) -> f a -> f b
  invCS eq = coCS (hither eq)

class EquivariantCS f => ContravariantCS (f :: Constraint -> *) where
  contraCS :: (a :<= b) -> f b -> f a

class EquivariantCS f => CovariantCS (f :: Constraint -> *) where
  coCS :: (a :<= b) -> f a -> f b

instance EquivariantCS Dict
instance CovariantCS Dict where
  coCS f Dict = Dict // f

instance EquivariantCS ((:<=) a)
instance CovariantCS ((:<=) a) where
  coCS = o

instance EquivariantCS ((:~) a) where
  invCS = undefined

eqvSymm :: a :~ b -> b :~ a
eqvSymm (Equiv a b) = Equiv b a

eqvEq :: (a ~ b) => a :~ b
eqvEq = Equiv Dict Dict

idEq :: (a ~ a) :~ ()
idEq = Equiv Dict Dict

class Closed a | -> a
instance Closed ()

-- an uninhabitable constraint
type Bottom = Closed [()]

-- initial arrow
bottom :: Bottom :<= a
bottom = bottom

type Not a = a :<= Bottom

class Tautology (c :: Constraint) where
  taut :: Top :<= c
instance Tautology (Instance ()) where taut = Sub Dict
instance (Tautology a, Tautology b) => Tautology (a, b) where taut = taut &&& taut
instance (Tautology (Instance a), Tautology (Instance b)) => Tautology (Instance (a, b)) where
  taut = Sub (Dict // ((taut :: Top :<= Instance a) &&& (taut :: Top :<= Instance b)))
instance Tautology (Class () (Class () h)) where taut = Sub Dict
instance Tautology (Eq ()) where taut = Sub Dict
instance Tautology (Instance (Eq ())) where taut = Sub Dict
instance Tautology (Eq Int) where taut = Sub Dict
instance Tautology (Instance (Eq Int)) where taut = Sub Dict

-- data Sum :: Constraint -> Constraint -> * where
--  LeftC :: a => Sum a b
--  RightC :: b => Sum a b

-- constraint coproduct
-- class (:+) (a :: Constraint) (b :: Constraint) where sum :: Sum a b

-- would obviously overlap
-- instance a => a :+ b where sum = LeftC
-- instance b => a :+ b where sum = RightC

-- orS :: (a :<= b) -> (c :<= d) -> (a :+ c) :<= (b :+ d)
--orS f g = Sub (case sum :: Sum a c of
--   LeftC  -> Dict // f
--   RightC -> Dict // g)

-- orS :: (a :<= b) -> (c :<= d) -> (a :+ c) :<= (b :+ d)
-- orS 

-- bimapS

-- orS ::
