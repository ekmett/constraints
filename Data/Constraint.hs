{-# LANGUAGE
  FunctionalDependencies,
  UndecidableInstances,
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

module Data.Constraint
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
  -- * class and instance declarations
  , Class(cls)
  , (:=>)(ins)
  ) where

import Control.Monad
import Control.Monad.Instances
import Control.Applicative
import Data.Semigroup
import Unsafe.Coerce

data Dict :: Constraint -> * where
  Dict :: a => Dict a

infixr 9 :-
-- entailment
data (:-) :: Constraint -> Constraint -> * where
  Sub :: (a => Dict b) -> a :- b

infixl 1 \\
(\\) :: a => (b => r) -> (a :- b) -> r
r \\ Sub Dict = r

class Class (b :: Constraint) (h :: Constraint) | h -> b where
  cls :: h :- b

class Cls (h :: Constraint) where
  type Super h :: Constraint
  type Super h = ()
  cs :: h :- Super h
  default cs :: h :- ()
  cs = Sub Dict

class Ins (h :: Constraint) where
  type Context h :: Constraint
  type Context h = ()
  is :: Context h :- h
  default is :: h => () :- h
  is = Sub Dict

instance Cls (Cls h)
instance Ins (Cls (Cls h))
instance Ins (Ins (Cls (Cls h)))

infixr 9 :=>
class (b :: Constraint) :=> (h :: Constraint) | h -> b where
  ins :: b :- h
-- no default implementations for MPTCs, even if they could fundep away to univariate TCs
--  default ins :: h => () :- h
--  ins = Sub Dict

instance               Class () (Class b h) where cls = Sub Dict
instance        () :=> Class () (Class b h) where ins = Sub Dict
instance () :=> () :=> Class () (Class b h) where ins = Sub Dict


instance               Class () (b :=> h) where cls = Sub Dict
instance        () :=> Class () (b :=> h) where ins = Sub Dict
instance () :=> () :=> Class () (b :=> h) where ins = Sub Dict

-- bootstrap instance entries for the instance class itself beyond the two base cases
instance (caa :=> ca :=> a) => (ca :=> a) :=> caa :=> ca :=> a where ins = Sub Dict

-- admissable instances for products and units
instance               Class () () where cls = Sub Dict
instance        () :=> Class () () where ins = Sub Dict
instance () :=> () :=> Class () () where ins = Sub Dict

instance        (Class ca a, Class cb b)  => Class (ca, cb) (a, b) where cls = cls *** cls
instance        (Class ca a, Class cb b) :=> Class (ca, cb) (a, b) where ins = Sub Dict
instance () :=> (Class ca a, Class cb b) :=> Class (ca, cb) (a, b) where ins = Sub Dict

instance        () :=> () where ins = Sub Dict
instance () :=> () :=> () where ins = Sub Dict

instance (ca :=> a, cb :=> b) => (ca, cb) :=> (a, b) where
  ins = Sub $ Dict \\ (ins :: ca :- a) *** (ins :: cb :- b)

instance (caa :=> ca :=> a, cbb :=> cb :=> b) => ((caa, cbb) :=> (ca, cb) :=> (a, b)) where
  ins = Sub $ Dict \\ ((ins :: caa :- (ca :=> a)) *** (ins :: cbb :- (cb :=> b)))

-- instances for Dict
instance () :=> () :=> Eq (Dict a) where ins = Sub Dict
instance        () :=> Eq (Dict a) where ins = Sub Dict
instance               Eq (Dict a) where
  Dict == Dict = True

instance () :=> () :=> Ord (Dict a) where ins = Sub Dict
instance        () :=> Ord (Dict a) where ins = Sub Dict
instance               Ord (Dict a) where
  compare Dict Dict = EQ

instance () :=> a :=> Enum (Dict a) where ins = Sub Dict
instance        a :=> Enum (Dict a) where ins = Sub Dict
instance        a  => Enum (Dict a) where
  toEnum _ = Dict
  fromEnum Dict = 0

instance () :=> a :=> Bounded (Dict a) where ins = Sub Dict
instance        a :=> Bounded (Dict a) where ins = Sub Dict
instance        a  => Bounded (Dict a) where
  minBound = Dict
  maxBound = Dict

instance () :=> () :=> Show (Dict a) where ins = Sub Dict
instance        () :=> Show (Dict a) where ins = Sub Dict
instance               Show (Dict a) where
  showsPrec _ Dict = showString "Dict"


instance () :=> a :=> Read (Dict a) where ins = Sub Dict
instance        a :=> Read (Dict a) where ins = Sub Dict
instance        a  => Read (Dict a) where
  readsPrec d = readParen (d > 10) $ \s ->
    [ (Dict, t) | ("Dict", t) <- lex s ]

-- instance Semigroup (Dict a) where Dict <> Dict = Dict
-- instance        () :=> Semigroup (Dict a) where ins = Sub Dict
-- instance () :=> () :=> Semigroup (Dict a) where ins = Sub Dict

instance () :=> a :=> Monoid (Dict a) where ins = Sub Dict
instance        a :=> Monoid (Dict a) where ins = Sub Dict
instance        a  => Monoid (Dict a) where
  mappend Dict Dict = Dict
  mempty = Dict

-- instances for entailment
instance () :=> () :=> Eq (a :- b) where ins = Sub Dict
instance        () :=> Eq (a :- b) where ins = Sub Dict
instance               Eq (a :- b) where
  Sub _ == Sub _ = True

instance () :=> () :=> Ord (a :- b) where ins = Sub Dict
instance        () :=> Ord (a :- b) where ins = Sub Dict
instance               Ord (a :- b) where
  compare (Sub _) (Sub _) = EQ


instance () :=> () :=> Show (a :- b) where ins = Sub Dict
instance        () :=> Show (a :- b) where ins = Sub Dict
instance               Show (a :- b) where
  showsPrec d (Sub _) = showParen (d > 10) $ showString "Sub Dict"


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

-- When we get polymorphic kinds:
-- class Category (k :: x -> x -> *) where
--   id :: k a a
--   (.) :: k b c -> k a b -> k a c

-- instance Category (:-) where
--   id = refl
--   (.) = trans

(***) :: (a :- b) -> (c :- d) -> (a, c) :- (b, d)
f *** g = Sub $ Dict \\ f \\ g

-- terminal arrows
top :: a :- ()
top = Sub Dict

-- bimap for the product bifunctor
-- due to the hack for the kind of (,) in the compiler we can't actually make a bifunctor!

-- Prelude instances

-- Eq
instance () :=> () :=> Class () (Eq a) where ins = Sub Dict
instance        () :=> Class () (Eq a) where ins = Sub Dict
instance               Class () (Eq a) where cls = Sub Dict

instance () :=> () :=> Eq () where ins = Sub Dict
instance        () :=> Eq () where ins = Sub Dict

instance () :=> () :=> Eq Int where ins = Sub Dict
instance        () :=> Eq Int where ins = Sub Dict

instance () :=> Eq a :=> Eq [a] where ins = Sub Dict
instance        Eq a :=> Eq [a] where ins = Sub Dict

instance () :=> (Eq a, Eq b) :=> Eq (a, b) where ins = Sub Dict
instance        (Eq a, Eq b) :=> Eq (a, b) where ins = Sub Dict

-- Ord
instance () :=> () :=> Class (Eq a) (Ord a) where ins = Sub Dict
instance        () :=> Class (Eq a) (Ord a) where ins = Sub Dict
instance               Class (Eq a) (Ord a) where cls = Sub Dict

instance () :=> () :=> Ord () where ins = Sub Dict
instance        () :=> Ord () where ins = Sub Dict

instance () :=> () :=> Ord Int where ins = Sub Dict
instance        () :=> Ord Int where ins = Sub Dict

instance () :=> Ord a :=> Ord [a] where ins = Sub Dict
instance        Ord a :=> Ord [a] where ins = Sub Dict

instance () :=> (Ord a, Ord b) :=> Ord (a, b) where ins = Sub Dict
instance        (Ord a, Ord b) :=> Ord (a, b) where ins = Sub Dict

-- Enum
instance () :=> () :=> Class () (Enum a) where ins = Sub Dict
instance        () :=> Class () (Enum a) where ins = Sub Dict
instance               Class () (Enum a) where cls = Sub Dict

instance () :=> Class () (Bounded a) where ins = Sub Dict
instance        Class () (Bounded a) where cls = Sub Dict

instance () :=> Class () (Num a) where ins = Sub Dict
instance        Class () (Num a) where cls = Sub Dict

-- Semigroup
instance () :=> () :=> Class () (Semigroup a) where ins = Sub Dict
instance        () :=> Class () (Semigroup a) where ins = Sub Dict
instance               Class () (Semigroup a) where cls = Sub Dict

instance Monoid w :=> Semigroup (WrappedMonoid w) where ins = Sub Dict

-- Monoid
instance () :=> () :=> Class () (Monoid a) where ins = Sub Dict
instance        () :=> Class () (Monoid a) where ins = Sub Dict
instance               Class () (Monoid a) where cls = Sub Dict

-- Functor
instance () :=> () :=> Class () (Functor f) where ins = Sub Dict
instance        () :=> Class () (Functor f) where ins = Sub Dict
instance               Class () (Functor f) where cls = Sub Dict

instance () :=> () :=> Functor [] where ins = Sub Dict
instance        () :=> Functor [] where ins = Sub Dict

instance () :=> () :=> Functor Maybe where ins = Sub Dict
instance        () :=> Functor Maybe where ins = Sub Dict

instance () :=> () :=> Functor ((->) a) where ins = Sub Dict
instance        () :=> Functor ((->) a) where ins = Sub Dict

instance () :=> () :=> Functor ((,) a) where ins = Sub Dict
instance        () :=> Functor ((,) a) where ins = Sub Dict

instance Monad m :=> Functor (WrappedMonad m) where ins = Sub Dict

-- Applicative
instance () :=> () :=> Class (Functor f) (Applicative f) where ins = Sub Dict
instance        () :=> Class (Functor f) (Applicative f) where ins = Sub Dict
instance               Class (Functor f) (Applicative f) where cls = Sub Dict

instance () :=> () :=> Applicative [] where ins = Sub Dict
instance        () :=> Applicative [] where ins = Sub Dict

instance () :=> () :=> Applicative Maybe where ins = Sub Dict
instance        () :=> Applicative Maybe where ins = Sub Dict

instance () :=> () :=> Applicative ((->) a) where ins = Sub Dict
instance        () :=> Applicative ((->) a) where ins = Sub Dict

instance () :=> Monoid w :=> Applicative ((,) w) where ins = Sub Dict
instance        Monoid w :=> Applicative ((,) w) where ins = Sub Dict

instance Monad m :=> Applicative (WrappedMonad m) where ins = Sub Dict

-- Alternative
instance () :=> () :=> Class (Applicative f) (Alternative f) where ins = Sub Dict
instance        () :=> Class (Applicative f) (Alternative f) where ins = Sub Dict
instance               Class (Applicative f) (Alternative f) where cls = Sub Dict

instance () :=> () :=> Alternative [] where ins = Sub Dict
instance        () :=> Alternative [] where ins = Sub Dict

instance () :=> () :=> Alternative Maybe where ins = Sub Dict
instance        () :=> Alternative Maybe where ins = Sub Dict

instance MonadPlus m :=> Alternative (WrappedMonad m) where ins = Sub Dict

-- Monad
instance () :=> () :=> Class () (Monad f) where ins = Sub Dict
instance        () :=> Class () (Monad f) where ins = Sub Dict
instance               Class () (Monad f) where cls = Sub Dict

instance () :=> () :=> Monad [] where ins = Sub Dict
instance        () :=> Monad [] where ins = Sub Dict

instance () :=> () :=> Monad ((->) a) where ins = Sub Dict
instance        () :=> Monad ((->) a) where ins = Sub Dict

-- MonadPlus
instance () :=> () :=> Class (Monad f) (MonadPlus f) where ins = Sub Dict
instance        () :=> Class (Monad f) (MonadPlus f) where ins = Sub Dict
instance               Class (Monad f) (MonadPlus f) where cls = Sub Dict

instance () :=> () :=> MonadPlus [] where ins = Sub Dict
instance        () :=> MonadPlus [] where ins = Sub Dict

instance () :=> () :=> MonadPlus Maybe where ins = Sub Dict
instance        () :=> MonadPlus Maybe where ins = Sub Dict

-- unsafe local instance resolution

evil :: a :- b
evil = unsafeCoerce refl

applicative :: forall m a. Monad m => (Applicative m => m a) -> m a
applicative m = m \\ trans (evil :: Applicative (WrappedMonad m) :- Applicative m) ins

alternative :: forall m a. MonadPlus m => (Alternative m => m a) -> m a
alternative m = m \\ trans (evil :: Alternative (WrappedMonad m) :- Alternative m) ins

semigroup :: forall w. Monoid w => (Semigroup w => w) -> w
semigroup m = m \\ trans (evil :: Semigroup (WrappedMonoid w) :- Semigroup w) ins

-- Using applicative sugar given only a monad
(<&>) :: Monad m => m a -> m b -> m (a, b)
m <&> n = applicative $ (,) <$> m <*> n
