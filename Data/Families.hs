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
{-# LANGUAGE UndecidableInstances #-}
#define UNDECIDABLE

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
  , C(..)
  , I(..)
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

infixl 1 \\ -- required comment
(\\) :: a => (b => r) -> (a :- b) -> r
r \\ Sub Dict = r

class C (h :: Constraint) where
  type Sup h :: Constraint
  type Sup h = ()
  cls :: h :- Sup h
  default cls :: h :- ()
  cls = Sub Dict

class I (h :: Constraint) where
  type Ctx h :: Constraint
  type Ctx h = ()
  ins :: Ctx h :- h
  default ins :: h => Ctx h :- h
  ins = Sub Dict

(***) :: (a :- b) -> (c :- d) -> (a, c) :- (b, d)
f *** g = Sub $ Dict \\ f \\ g

instance C a => I (C a)

instance C (C a)
instance C (I a)

-- decidable, patched in current GHC
#ifdef UNDECIDABLE
instance I a => I (I a)
#endif

instance C ()
instance I ()

instance I (Eq (Dict a))
instance Eq (Dict a) where
  Dict == Dict = True

instance I (Ord (Dict a))
instance Ord (Dict a) where
  compare Dict Dict = EQ

#ifdef UNDECIDABLE
instance I (Enum (Dict a)) where
  type Ctx (Enum (Dict a)) = a
  ins = Sub Dict
instance a => Enum (Dict a) where
  toEnum _ = Dict
  fromEnum Dict = 0
#endif

#ifdef UNDECIDABLE
instance I (Bounded (Dict a)) where
  type Ctx (Bounded (Dict a)) = a
  ins = Sub Dict
instance a => Bounded (Dict a) where
  minBound = Dict
  maxBound = Dict
#endif

instance I (Show (Dict a))
instance Show (Dict a) where
  showsPrec _ Dict = showString "Dict"

#ifdef UNDECIDABLE
instance I (Read (Dict a)) where
  type Ctx (Read (Dict a)) = a
  ins = Sub Dict
instance a => Read (Dict a) where
  readsPrec d = readParen (d > 10) $ \s ->
    [ (Dict, t) | ("Dict", t) <- lex s ]
#endif

instance I (Semigroup (Dict a))
instance Semigroup (Dict a) where
  Dict <> Dict = Dict

#ifdef UNDECIDABLE
instance I (Monoid (Dict a)) where
  type Ctx (Monoid (Dict a)) = a
  ins = Sub Dict
instance a => Monoid (Dict a) where
  mappend Dict Dict = Dict
  mempty = Dict
#endif

instance I (Eq (a :- b))
instance Eq (a :- b) where
  Sub _ == Sub _ = True

instance I (Ord (a :- b))
instance Ord (a :- b) where
  compare (Sub _) (Sub _) = EQ

instance I (Show (a :- b))
instance Show (a :- b) where
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

-- terminal arrows
top :: a :- ()
top = Sub Dict

evil :: a :- b
evil = unsafeCoerce refl

-- bimap for the product bifunctor
-- due to the hack for the kind of (,) in the compiler we can't actually make a bifunctor!

-- Prelude instances

-- Eq
instance C (Eq a)
instance I (Eq ())
instance I (Eq Int)
instance I (Eq [a]) where
  type Ctx (Eq [a]) = Eq a
  ins = Sub Dict
instance I (Eq (a,b)) where
  type Ctx (Eq (a,b)) = (Eq a, Eq b)
  ins = Sub Dict

-- Ord
instance C (Ord a) where
  type Sup (Ord a) = Eq a
  cls = Sub Dict
instance I (Ord ())
instance I (Ord Int)
instance I (Ord [a]) where
  type Ctx (Ord [a]) = Ord a
  ins = Sub Dict
instance I (Ord (a, b)) where
  type Ctx (Ord (a, b)) = (Ord a, Ord b)
  ins = Sub Dict

instance C (Enum a)
instance I (Enum Int)

instance C (Bounded a)

instance C (Num a)

instance C (Semigroup a)
instance I (Semigroup (WrappedMonoid w)) where
  type Ctx (Semigroup (WrappedMonoid w)) = Monoid w
  ins = Sub Dict

semigroup :: forall w. Monoid w => (Semigroup w => w) -> w
semigroup m = m \\ trans (evil :: Semigroup (WrappedMonoid w) :- Semigroup w) ins

instance C (Monoid a)

instance C (Functor f)
instance I (Functor [])
instance I (Functor Maybe)
instance I (Functor ((->) a))
instance I (Functor ((,) a))
instance I (Functor (WrappedMonad m)) where
  type Ctx (Functor (WrappedMonad m)) = Monad m
  ins = Sub Dict

instance C (Applicative f) where
  type Sup (Applicative f) = Functor f
  cls = Sub Dict
instance I (Applicative [])
instance I (Applicative Maybe)
instance I (Applicative ((->)a))
instance I (Applicative ((,)a)) where
  type Ctx (Applicative ((,)a)) = Monoid a
  ins = Sub Dict
instance I (Applicative (WrappedMonad m)) where
  type Ctx (Applicative (WrappedMonad m)) = Monad m
  ins = Sub Dict

applicative :: forall m a. Monad m => (Applicative m => m a) -> m a
applicative m = m \\ trans (evil :: Applicative (WrappedMonad m) :- Applicative m) ins

instance C (Alternative f) where
  type Sup (Alternative f) = Applicative f
  cls = Sub Dict
instance I (Alternative [])
instance I (Alternative Maybe)
instance I (Alternative (WrappedMonad m)) where
  type Ctx (Alternative (WrappedMonad m)) = MonadPlus m
  ins = Sub Dict

alternative :: forall m a. MonadPlus m => (Alternative m => m a) -> m a
alternative m = m \\ trans (evil :: Alternative (WrappedMonad m) :- Alternative m) ins

instance C (Monad f)
instance I (Monad [])
instance I (Monad ((->) a))

instance C (MonadPlus f)
instance I (MonadPlus [])
instance I (MonadPlus Maybe)

-- example of using applicative sugar given only a monad
(<&>) :: Monad m => m a -> m b -> m (a, b)
m <&> n = applicative $ (,) <$> m <*> n
