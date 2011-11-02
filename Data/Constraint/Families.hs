{-# LANGUAGE
  CPP,
  ScopedTypeVariables,
  FlexibleInstances,
  FlexibleContexts,
  ConstraintKinds,
  KindSignatures,
  TypeOperators,
  Rank2Types,
  GADTs,
  DefaultSignatures,
  TypeFamilies
  #-}

-- {-# LANGUAGE UndecidableInstances #-}
-- #define UNDECIDABLE

module Data.Constraint.Families
  (
  -- * Dictionary
    Dict(Dict)
  -- * Entailment
  , (:-)(Sub)
  , (\\)
  , weaken1, weaken2, contract
  , (&&&), (***)
  , trans, refl
  , top
  -- * Reflection
  , Class(..)
  , Instance(..)
  -- * Sugar
  , applicative
  , alternative
  ) where

import Control.Monad
import Control.Monad.Instances
import Control.Applicative
import Data.Complex
import Data.Monoid
import Data.Ratio
import Unsafe.Coerce

data Dict :: Constraint -> * where
  Dict :: a => Dict a

instance Eq (Dict a) where
  Dict == Dict = True

instance Ord (Dict a) where
  compare Dict Dict = EQ

instance Show (Dict a) where
  showsPrec _ Dict = showString "Dict"

infixr 9 :-
-- entailment
data (:-) :: Constraint -> Constraint -> * where
  Sub :: (a => Dict b) -> a :- b

instance Eq (a :- b) where
  Sub _ == Sub _ = True

instance Ord (a :- b) where
  compare (Sub _) (Sub _) = EQ

instance Show (a :- b) where
  showsPrec d (Sub _) = showParen (d > 10) $ showString "Sub Dict"

infixl 1 \\ -- required comment
(\\) :: a => (b => r) -> (a :- b) -> r
r \\ Sub Dict = r

-- due to the hack for the kind of (,) in the compiler we can't actually make (,) a bifunctor!
(***) :: (a :- b) -> (c :- d) -> (a, c) :- (b, d)
f *** g = Sub $ Dict \\ f \\ g

-- weakening constraints / constraint product projections
weaken1 :: (a,b) :- a
weaken1 = Sub Dict

weaken2 :: (a,b) :- b
weaken2 = Sub Dict

-- contracting constraints / diagonal morphism
contract :: a :- (a, a)
contract = Sub Dict

-- constraint product
(&&&) :: (a :- b) -> (a :- c) -> a :- (b,c)
f &&& g = Sub $ Dict \\ f \\ g

-- transitivity of entailment
trans :: (b :- c) -> (a :- b) -> a :- c
trans f g = Sub $ Dict \\ f \\ g

-- reflexivity
refl :: a :- a
refl = Sub Dict

-- terminal arrows
top :: a :- ()
top = Sub Dict

-- don't do this!
evil :: a :- b
evil = unsafeCoerce refl

class Class (h :: Constraint) where
  type Sup h :: Constraint
  type Sup h = ()
  cls :: h :- Sup h
  default cls :: h :- ()
  cls = Sub Dict

class Instance (h :: Constraint) where
  type Ctx h :: Constraint
  type Ctx h = ()
  ins :: Ctx h :- h
  default ins :: h => Ctx h :- h
  ins = Sub Dict

instance Class (Class a)
instance Class (Instance a)

-- bootstrapping

#ifdef UNDECIDABLE
instance Class a => Instance (Class a)
instance Instance a => Instance (Instance a)
#endif

instance Class ()
instance Instance ()

-- Local, Prelude, Applicative, C.M.I, Data.Monoid instances

-- Eq
instance Class (Eq a)
instance Instance (Eq ())
instance Instance (Eq Int)
instance Instance (Eq Bool)
instance Instance (Eq Integer)
instance Instance (Eq Float)
instance Instance (Eq Double)
instance Instance (Eq [a]) where
  type Ctx (Eq [a]) = Eq a
  ins = Sub Dict
instance Instance (Eq (Maybe a)) where
  type Ctx (Eq (Maybe a)) = Eq a
  ins = Sub Dict
instance Instance (Eq (Complex a)) where
  type Ctx (Eq (Complex a)) = Eq a
  ins = Sub Dict
instance Instance (Eq (Ratio a)) where
  type Ctx (Eq (Ratio a)) = Eq a
  ins = Sub Dict
instance Instance (Eq (a, b)) where
  type Ctx (Eq (a,b)) = (Eq a, Eq b)
  ins = Sub Dict
instance Instance (Eq (Either a b)) where
  type Ctx (Eq (Either a b)) = (Eq a, Eq b)
  ins = Sub Dict
instance Instance (Eq (Dict a))
instance Instance (Eq (a :- b))

-- Ord
instance Class (Ord a) where
  type Sup (Ord a) = Eq a
  cls = Sub Dict
instance Instance (Ord ())
instance Instance (Ord Bool)
instance Instance (Ord Int)
instance Instance (Ord Integer)
instance Instance (Ord Float)
instance Instance (Ord Double)
instance Instance (Ord Char)
instance Instance (Ord (Maybe a)) where
  type Ctx (Ord (Maybe a)) = Ord a
  ins = Sub Dict
instance Instance (Ord [a]) where
  type Ctx (Ord [a]) = Ord a
  ins = Sub Dict
instance Instance (Ord (a, b)) where
  type Ctx (Ord (a, b)) = (Ord a, Ord b)
  ins = Sub Dict
instance Instance (Ord (Either a b)) where
  type Ctx (Ord (Either a b)) = (Ord a, Ord b)
  ins = Sub Dict
instance Instance (Ord (Ratio a)) where
  type Ctx (Ord (Ratio a)) = Integral a
  ins = Sub Dict
instance Instance (Ord (Dict a))
instance Instance (Ord (a :- b))

instance Class (Show a)
instance Instance (Show ())
instance Instance (Show Bool)
instance Instance (Show Ordering)
instance Instance (Show Char)
instance Instance (Show (Complex a)) where
  type Ctx (Show (Complex a)) = Show a
  ins = Sub Dict
instance Instance (Show [a]) where
  type Ctx (Show [a]) = Show a
  ins = Sub Dict
instance Instance (Show (Maybe a)) where
  type Ctx (Show (Maybe a)) = Show a
  ins = Sub Dict
instance Instance (Show (a, b)) where
  type Ctx (Show (a, b)) = (Show a, Show b)
  ins = Sub Dict
instance Instance (Show (Either a b)) where
  type Ctx (Show (Either a b)) = (Show a, Show b)
  ins = Sub Dict
instance Instance (Show (Ratio a)) where
  type Ctx (Show (Ratio a)) = (Integral a, Show a)
  ins = Sub Dict
instance Instance (Show (Dict a))
instance Instance (Show (a :- b))

instance Class (Read a)
instance Instance (Read ())
instance Instance (Read Bool)
instance Instance (Read Ordering)
instance Instance (Read Char)
instance Instance (Read (Complex a)) where
  type Ctx (Read (Complex a)) = Read a
  ins = Sub Dict
instance Instance (Read [a]) where
  type Ctx (Read [a]) = Read a
  ins = Sub Dict
instance Instance (Read (Maybe a)) where
  type Ctx (Read (Maybe a)) = Read a
  ins = Sub Dict
instance Instance (Read (a, b)) where
  type Ctx (Read (a, b)) = (Read a, Read b)
  ins = Sub Dict
instance Instance (Read (Either a b)) where
  type Ctx (Read (Either a b)) = (Read a, Read b)
  ins = Sub Dict
instance Instance (Read (Ratio a)) where
  type Ctx (Read (Ratio a)) = (Integral a, Read a)
  ins = Sub Dict

instance Class (Enum a)
instance Instance (Enum ())
instance Instance (Enum Bool)
instance Instance (Enum Ordering)
instance Instance (Enum Char)
instance Instance (Enum Int)
instance Instance (Enum Integer)
instance Instance (Enum Float)
instance Instance (Enum Double)
instance Instance (Enum (Ratio a)) where
  type Ctx (Enum (Ratio a)) = Integral a
  ins = Sub Dict

instance Class (Bounded a)
instance Instance (Bounded ())
instance Instance (Bounded Ordering)
instance Instance (Bounded Bool)
instance Instance (Bounded Int)
instance Instance (Bounded Char)
instance Instance (Bounded (a,b)) where
  type Ctx (Bounded (a,b)) = (Bounded a, Bounded b)
  ins = Sub Dict

instance Class (Num a)
instance Instance (Num Int)
instance Instance (Num Integer)
instance Instance (Num Float)
instance Instance (Num Double)
instance Instance (Num (Complex a)) where
  type Ctx (Num (Complex a)) = RealFloat a
  ins = Sub Dict
instance Instance (Num (Ratio a)) where
  type Ctx (Num (Ratio a)) = Integral a
  ins = Sub Dict

instance Class (Real a) where
  type Sup (Real a) = (Num a, Ord a)
  cls = Sub Dict
instance Instance (Real Int)
instance Instance (Real Integer)
instance Instance (Real Float)
instance Instance (Real Double)
instance Instance (Real (Ratio a)) where
  type Ctx (Real (Ratio a)) = Integral a
  ins = Sub Dict

instance Class (Integral a) where
  type Sup (Integral a) = (Real a, Enum a)
  cls = Sub Dict
instance Instance (Integral Int)
instance Instance (Integral Integer)

instance Class (Fractional a) where
  type Sup (Fractional a) = Num a
  cls = Sub Dict
instance Instance (Fractional Float)
instance Instance (Fractional Double)
instance Instance (Fractional (Complex a)) where
  type Ctx (Fractional (Complex a)) = RealFloat a
  ins = Sub Dict
instance Instance (Fractional (Ratio a)) where
  type Ctx (Fractional (Ratio a)) = Integral a
  ins = Sub Dict

instance Class (Floating a) where
  type Sup (Floating a) = Fractional a
  cls = Sub Dict
instance Instance (Floating Float)
instance Instance (Floating Double)
instance Instance (Floating (Complex a)) where
  type Ctx (Floating (Complex a)) = RealFloat a
  ins = Sub Dict

instance Class (RealFrac a) where
  type Sup (RealFrac a) = (Real a, Fractional a)
  cls = Sub Dict
instance Instance (RealFrac Float)
instance Instance (RealFrac Double)
instance Instance (RealFrac (Ratio a)) where
  type Ctx (RealFrac (Ratio a)) = Integral a
  ins = Sub Dict

instance Class (RealFloat a) where
  type Sup (RealFloat a) = (RealFrac a, Floating a)
  cls = Sub Dict
instance Instance (RealFloat Float)
instance Instance (RealFloat Double)

instance Class (Monoid a)
instance Instance (Monoid ())
instance Instance (Monoid Ordering)
instance Instance (Monoid [a])
instance Instance (Monoid (Maybe a)) where
  type Ctx (Monoid (Maybe a)) = Monoid a -- blech
  ins = Sub Dict
instance Instance (Monoid (a, b)) where
  type Ctx (Monoid (a, b)) = (Monoid a, Monoid b)
  ins = Sub Dict

instance Class (Functor f)
instance Instance (Functor [])
instance Instance (Functor Maybe)
instance Instance (Functor (Either a))
instance Instance (Functor ((->) a))
instance Instance (Functor ((,) a))
instance Instance (Functor IO)
instance Instance (Functor (WrappedMonad m)) where
  type Ctx (Functor (WrappedMonad m)) = Monad m
  ins = Sub Dict

instance Class (Applicative f) where
  type Sup (Applicative f) = Functor f
  cls = Sub Dict
instance Instance (Applicative [])
instance Instance (Applicative Maybe)
instance Instance (Applicative (Either a))
instance Instance (Applicative ((->)a))
instance Instance (Applicative IO)
instance Instance (Applicative ((,)a)) where
  type Ctx (Applicative ((,)a)) = Monoid a
  ins = Sub Dict
instance Instance (Applicative (WrappedMonad m)) where
  type Ctx (Applicative (WrappedMonad m)) = Monad m
  ins = Sub Dict

instance Class (Alternative f) where
  type Sup (Alternative f) = Applicative f
  cls = Sub Dict
instance Instance (Alternative [])
instance Instance (Alternative Maybe)
instance Instance (Alternative (WrappedMonad m)) where
  type Ctx (Alternative (WrappedMonad m)) = MonadPlus m
  ins = Sub Dict

instance Class (Monad f)
instance Instance (Monad [])
instance Instance (Monad ((->) a))
instance Instance (Monad (Either a))
instance Instance (Monad IO)

instance Class (MonadPlus f)
instance Instance (MonadPlus [])
instance Instance (MonadPlus Maybe)

-- local UndecidableInstances, due to polymorphic class constraints
#ifdef UNDECIDABLE
instance Instance (Enum (Dict a)) where
  type Ctx (Enum (Dict a)) = a
  ins = Sub Dict

instance a => Enum (Dict a) where
  toEnum _ = Dict
  fromEnum Dict = 0

instance Instance (Bounded (Dict a)) where
  type Ctx (Bounded (Dict a)) = a
  ins = Sub Dict

instance a => Bounded (Dict a) where
  minBound = Dict
  maxBound = Dict

instance Instance (Read (Dict a)) where
  type Ctx (Read (Dict a)) = a
  ins = Sub Dict

instance a => Read (Dict a) where
  readsPrec d = readParen (d > 10) $ \s ->
    [ (Dict, t) | ("Dict", t) <- lex s ]

instance Instance (Monoid (Dict a)) where
  type Ctx (Monoid (Dict a)) = a
  ins = Sub Dict

instance a => Monoid (Dict a) where
  mappend Dict Dict = Dict
  mempty = Dict
#endif


applicative :: forall m a. Monad m => (Applicative m => m a) -> m a
applicative m = m \\ trans (evil :: Applicative (WrappedMonad m) :- Applicative m) ins

alternative :: forall m a. MonadPlus m => (Alternative m => m a) -> m a
alternative m = m \\ trans (evil :: Alternative (WrappedMonad m) :- Alternative m) ins

-- Using applicative sugar given just a monad, no lifting needed
(<&>) :: Monad m => m a -> m b -> m (a, b)
m <&> n = applicative $ (,) <$> m <*> n

