{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE UnicodeSyntax #-}

-- |
-- Copyright   :  (C) 2011-2015 Edward Kmett,
-- License     :  BSD-style (see the file LICENSE)
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  experimental
-- Portability :  non-portable
--
-- @ConstraintKinds@ made type classes into types of a new kind, @Constraint@.
--
-- @
-- 'Eq' :: * -> 'Constraint'
-- 'Ord' :: * -> 'Constraint'
-- 'Monad' :: (* -> *) -> 'Constraint'
-- @
--
-- The need for this extension was first publicized in the paper
--
-- <https://www.microsoft.com/en-us/research/wp-content/uploads/2016/07/gmap3.pdf Scrap your boilerplate with class: extensible generic functions>
--
-- by Ralf Lämmel and Simon Peyton Jones in 2005, which shoehorned all the
-- things they needed into a custom 'Sat' typeclass.
--
-- With @ConstraintKinds@ we can put into code a lot of tools for manipulating
-- these new types without such awkward workarounds.

module Data.Constraint
  (
  -- * The Kind of Constraints
    Constraint
  -- * Dictionary
  , Dict(Dict)
  , HasDict(..)
  , withDict
  , (\\)
  -- * Entailment
  , (:-)(Sub)
  , type (⊢)
  , type (|-)
  , type (&)
  , weaken1, weaken2, contract
  , strengthen1, strengthen2
  , (&&&), (***)
  , trans, refl
  , implied
  , Bottom(no)
  , top, bottom
  -- * Dict is fully faithful
  , mapDict
  , unmapDict
  -- * Reflection
  , Class(..)
  , (:=>)(..)
  ) where
import Control.Applicative
import Control.Category
import Control.DeepSeq
import Control.Monad
import Data.Complex
import Data.Ratio
import Data.Data hiding (TypeRep)
import qualified GHC.Exts as Exts (Any)
import GHC.Exts (Constraint)
import Data.Bits (Bits)
import Data.Functor.Identity (Identity)
import Numeric.Natural (Natural)
import Data.Coerce (Coercible)
import Data.Type.Coercion(Coercion(..))
import Data.Type.Equality (type (~~))
import qualified Data.Type.Equality as Hetero
import Type.Reflection (TypeRep, typeRepKind, withTypeable)
import Data.Boring (Boring (..))

-- | Values of type @'Dict' p@ capture a dictionary for a constraint of type @p@.
--
-- e.g.
--
-- @
-- 'Dict' :: 'Dict' ('Eq' 'Int')
-- @
--
-- captures a dictionary that proves we have an:
--
-- @
-- instance 'Eq' 'Int'
-- @
--
-- Pattern matching on the 'Dict' constructor will bring this instance into scope.
--
data Dict :: Constraint -> * where
  Dict :: a => Dict a

deriving stock instance (Typeable p, p) => Data (Dict p)
deriving stock instance Eq (Dict a)
deriving stock instance Ord (Dict a)
deriving stock instance Show (Dict a)

instance c => Boring (Dict c) where
    boring = Dict

{-
instance (Typeable p, p) => Data (Dict p) where
  gfoldl _ z Dict = z Dict
  toConstr _ = dictConstr
  gunfold _ z c = case constrIndex c of
    1 -> z Dict
    _ -> error "gunfold"
  dataTypeOf _ = dictDataType

dictConstr :: Constr
dictConstr = mkConstr dictDataType "Dict" [] Prefix

dictDataType :: DataType
dictDataType = mkDataType "Data.Constraint.Dict" [dictConstr]
-}


instance NFData (Dict c) where
  rnf Dict = ()

-- | Witnesses that a value of type @e@ contains evidence of the constraint @c@.
--
-- Mainly intended to allow ('\\') to be overloaded, since it's a useful operator.
class HasDict c e | e -> c where
  evidence :: e -> Dict c

instance HasDict a (Dict a) where
  evidence = Prelude.id

instance a => HasDict b (a :- b) where
  evidence (Sub x) = x

instance HasDict (Coercible a b) (Coercion a b) where
  evidence Coercion = Dict

instance HasDict (a ~ b) (a :~: b) where
  evidence Refl = Dict

instance HasDict (a ~~ b) (a Hetero.:~~: b) where
  evidence Hetero.HRefl = Dict

instance HasDict (Typeable k, Typeable a) (TypeRep (a :: k)) where
  evidence tr = withTypeable tr $ withTypeable (typeRepKind tr) Dict

-- | From a 'Dict', takes a value in an environment where the instance
-- witnessed by the 'Dict' is in scope, and evaluates it.
--
-- Essentially a deconstruction of a 'Dict' into its continuation-style
-- form.
--
-- Can also be used to deconstruct an entailment, @a ':-' b@, using a context @a@.
--
-- @
-- withDict :: 'Dict' c -> (c => r) -> r
-- withDict :: a => (a ':-' c) -> (c => r) -> r
-- @
withDict :: HasDict c e => e -> (c => r) -> r
withDict d r = case evidence d of
                 Dict -> r

infixl 1 \\ -- required comment

-- | Operator version of 'withDict', with the arguments flipped
(\\) :: HasDict c e => (c => r) -> e -> r
r \\ d = withDict d r

infixr 9 :-
infixr 9 ⊢

-- | Type entailment, as written with a single character.
type (⊢) = (:-)

-- | This is the type of entailment.
--
-- @a ':-' b@ is read as @a@ \"entails\" @b@.
--
-- With this we can actually build a category for 'Constraint' resolution.
--
-- e.g.
--
-- Because @'Eq' a@ is a superclass of @'Ord' a@, we can show that @'Ord' a@
-- entails @'Eq' a@.
--
-- Because @instance 'Ord' a => 'Ord' [a]@ exists, we can show that @'Ord' a@
-- entails @'Ord' [a]@ as well.
--
-- This relationship is captured in the ':-' entailment type here.
--
-- Since @p ':-' p@ and entailment composes, ':-' forms the arrows of a
-- 'Category' of constraints. However, 'Category' only became sufficiently
-- general to support this instance in GHC 7.8, so prior to 7.8 this instance
-- is unavailable.
--
-- But due to the coherence of instance resolution in Haskell, this 'Category'
-- has some very interesting properties. Notably, in the absence of
-- @IncoherentInstances@, this category is \"thin\", which is to say that
-- between any two objects (constraints) there is at most one distinguishable
-- arrow.
--
-- This means that for instance, even though there are two ways to derive
-- @'Ord' a ':-' 'Eq' [a]@, the answers from these two paths _must_ by
-- construction be equal. This is a property that Haskell offers that is
-- pretty much unique in the space of languages with things they call \"type
-- classes\".
--
-- What are the two ways?
--
-- Well, we can go from @'Ord' a ':-' 'Eq' a@ via the
-- superclass relationship, and then from @'Eq' a ':-' 'Eq' [a]@ via the
-- instance, or we can go from @'Ord' a ':-' 'Ord' [a]@ via the instance
-- then from @'Ord' [a] ':-' 'Eq' [a]@ through the superclass relationship
-- and this diagram by definition must \"commute\".
--
-- Diagrammatically,
--
-- >                    Ord a
-- >                ins /     \ cls
-- >                   v       v
-- >             Ord [a]     Eq a
-- >                cls \     / ins
-- >                     v   v
-- >                    Eq [a]
--
-- This safety net ensures that pretty much anything you can write with this
-- library is sensible and can't break any assumptions on the behalf of
-- library authors.
newtype a :- b = Sub (a => Dict b)

type role (:-) nominal nominal

instance (Typeable p, Typeable q, p => q) => Data (p :- q) where
  gfoldl _ z d = z d
  gunfold _ z c = case constrIndex c of
     1 -> z (Sub Dict)
     _ -> error "Data.Data.Data: Data.Constraint.:- constructor out of bounds"
  toConstr _ = subCon
  dataTypeOf _ = subTy

subCon :: Constr
subCon = mkConstr subTy "Sub Dict" [] Prefix
{-# noinline subCon #-}
subTy :: DataType
subTy = mkDataType "Data.Constraint.:-" [subCon]
{-# noinline subTy #-}

-- | Possible since GHC 7.8, when 'Category' was made polykinded.
instance Category (:-) where
  id  = refl
  (.) = trans

-- | Assumes 'IncoherentInstances' doesn't exist.
instance Eq (a :- b) where
  _ == _ = True

-- | Assumes 'IncoherentInstances' doesn't exist.
instance Ord (a :- b) where
  compare _ _ = EQ

instance Show (a :- b) where
  showsPrec d _ = showParen (d > 10) $ showString "Sub Dict"

instance a => NFData (a :- b) where
  rnf (Sub Dict) = ()

--------------------------------------------------------------------------------
-- Constraints form a Category
--------------------------------------------------------------------------------

-- | Transitivity of entailment
--
-- If we view @(':-')@ as a Constraint-indexed category, then this is @('.')@
trans :: (b :- c) -> (a :- b) -> a :- c
trans f g = Sub $ Dict \\ f \\ g

-- | Reflexivity of entailment
--
-- If we view @(':-')@ as a Constraint-indexed category, then this is 'id'
refl :: a :- a
refl = Sub Dict

--------------------------------------------------------------------------------
-- QuantifiedConstraints
--------------------------------------------------------------------------------

-- | Convert a quantified constraint into an entailment.
implied :: forall a b. (a => b) => a :- b
implied = Sub (Dict :: Dict b)

-- | The internal hom for the category of constraints.
--
-- This version can be passed around inside Dict, whereas (a => b) is impredicative
--
-- @
-- foo :: Dict (Ord a => Eq a)
-- foo = Dict
-- @
--
-- fails to typecheck due to the lack of impredicative polymorphism, but
--
-- @
-- foo :: Dict (Ord a |- Eq a)
-- foo = Dict
-- @
--
-- typechecks just fine.

class (p => q) => p |- q
instance (p => q) => p |- q


--------------------------------------------------------------------------------
-- (,) is a Bifunctor
--------------------------------------------------------------------------------

-- | due to the hack for the kind of @(,)@ in the current version of GHC we can't actually
-- make instances for @(,) :: Constraint -> Constraint -> Constraint@, but we can define
-- an equivalent type, that converts back and forth to @(,)@, and lets you hang instances.
class (p,q) => p & q
instance (p,q) => p & q

-- | due to the hack for the kind of @(,)@ in the current version of GHC we can't actually
-- make instances for @(,) :: Constraint -> Constraint -> Constraint@, but @(,)@ is a
-- bifunctor on the category of constraints. This lets us map over both sides.
(***) :: (a :- b) -> (c :- d) -> (a, c) :- (b, d)
f *** g = Sub $ Dict \\ f \\ g

--------------------------------------------------------------------------------
-- Constraints are Cartesian
--------------------------------------------------------------------------------

-- | Weakening a constraint product
--
-- The category of constraints is Cartesian. We can forget information.
weaken1 :: (a, b) :- a
weaken1 = Sub Dict

-- | Weakening a constraint product
--
-- The category of constraints is Cartesian. We can forget information.
weaken2 :: (a, b) :- b
weaken2 = Sub Dict

strengthen1 :: Dict b -> a :- c -> a :- (b,c)
strengthen1 d e = unmapDict (const d) &&& e

strengthen2 :: Dict b -> a :- c -> a :- (c,b)
strengthen2 d e = e &&& unmapDict (const d)

-- | Contracting a constraint / diagonal morphism
--
-- The category of constraints is Cartesian. We can reuse information.
contract :: a :- (a, a)
contract = Sub Dict

-- | Constraint product
--
-- > trans weaken1 (f &&& g) = f
-- > trans weaken2 (f &&& g) = g
(&&&) :: (a :- b) -> (a :- c) -> a :- (b, c)
f &&& g = Sub $ Dict \\ f \\ g

--------------------------------------------------------------------------------
-- Initial and terminal morphisms
--------------------------------------------------------------------------------

-- | Every constraint implies truth
--
-- These are the terminal arrows of the category, and @()@ is the terminal object.
--
-- Given any constraint there is a unique entailment of the @()@ constraint from that constraint.
top :: a :- ()
top = Sub Dict

-- | 'Any' inhabits every kind, including 'Constraint' but is uninhabited, making it impossible to define an instance.
class Exts.Any => Bottom where
  no :: a

-- |
-- This demonstrates the law of classical logic <http://en.wikipedia.org/wiki/Principle_of_explosion "ex falso quodlibet">
bottom :: Bottom :- a
bottom = Sub no

--------------------------------------------------------------------------------
-- Dict is fully faithful
--------------------------------------------------------------------------------

-- | Apply an entailment to a dictionary.
--
-- From a category theoretic perspective 'Dict' is a functor that maps from the category
-- of constraints (with arrows in ':-') to the category Hask of Haskell data types.
mapDict :: (a :- b) -> Dict a -> Dict b
mapDict p Dict = case p of Sub q -> q

-- |
-- This functor is fully faithful, which is to say that given any function you can write
-- @Dict a -> Dict b@ there also exists an entailment @a :- b@ in the category of constraints
-- that you can build.
unmapDict :: (Dict a -> Dict b) -> a :- b
unmapDict f = Sub (f Dict)

type role Dict nominal

--------------------------------------------------------------------------------
-- Reflection
--------------------------------------------------------------------------------

-- | Reify the relationship between a class and its superclass constraints as a class
--
-- Given a definition such as
--
-- @
-- class Foo a => Bar a
-- @
--
-- you can capture the relationship between 'Bar a' and its superclass 'Foo a' with
--
-- @
-- instance 'Class' (Foo a) (Bar a) where 'cls' = 'Sub' 'Dict'
-- @
--
-- Now the user can use 'cls :: Bar a :- Foo a'
class Class b h | h -> b where
  cls :: h :- b

infixr 9 :=>
-- | Reify the relationship between an instance head and its body as a class
--
-- Given a definition such as
--
-- @
-- instance Foo a => Foo [a]
-- @
--
-- you can capture the relationship between the instance head and its body with
--
-- @
-- instance Foo a ':=>' Foo [a] where 'ins' = 'Sub' 'Dict'
-- @
class b :=> h | h -> b where
  ins :: b :- h

-- Bootstrapping

instance Class () (Class b a) where cls = Sub Dict
instance Class () (b :=> a) where cls = Sub Dict

instance Class b a => () :=> Class b a where ins = Sub Dict
instance (b :=> a) => () :=> (b :=> a) where ins = Sub Dict

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
instance () :=> Eq Word where ins = Sub Dict
instance Eq a :=> Eq (Identity a) where ins = Sub Dict
instance Eq a :=> Eq (Const a b) where ins = Sub Dict
instance () :=> Eq Natural where ins = Sub Dict

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
instance () :=> Ord Word where ins = Sub Dict
instance Ord a :=> Ord (Identity a) where ins = Sub Dict
instance Ord a :=> Ord (Const a b) where ins = Sub Dict
instance () :=> Ord Natural where ins = Sub Dict

-- Show
instance Class () (Show a) where cls = Sub Dict
instance () :=> Show () where ins = Sub Dict
instance () :=> Show Bool where ins = Sub Dict
instance () :=> Show Ordering where ins = Sub Dict
instance () :=> Show Char where ins = Sub Dict
instance () :=> Show Int where ins = Sub Dict
instance Show a :=> Show (Complex a) where ins = Sub Dict
instance Show a :=> Show [a] where ins = Sub Dict
instance Show a :=> Show (Maybe a) where ins = Sub Dict
instance (Show a, Show b) :=> Show (a, b) where ins = Sub Dict
instance (Show a, Show b) :=> Show (Either a b) where ins = Sub Dict
instance (Integral a, Show a) :=> Show (Ratio a) where ins = Sub Dict
instance () :=> Show (Dict a) where ins = Sub Dict
instance () :=> Show (a :- b) where ins = Sub Dict
instance () :=> Show Word where ins = Sub Dict
instance Show a :=> Show (Identity a) where ins = Sub Dict
instance Show a :=> Show (Const a b) where ins = Sub Dict
instance () :=> Show Natural where ins = Sub Dict

-- Read
instance Class () (Read a) where cls = Sub Dict
instance () :=> Read () where ins = Sub Dict
instance () :=> Read Bool where ins = Sub Dict
instance () :=> Read Ordering where ins = Sub Dict
instance () :=> Read Char where ins = Sub Dict
instance () :=> Read Int where ins = Sub Dict
instance Read a :=> Read (Complex a) where ins = Sub Dict
instance Read a :=> Read [a] where ins = Sub Dict
instance Read a :=> Read (Maybe a) where ins = Sub Dict
instance (Read a, Read b) :=> Read (a, b) where ins = Sub Dict
instance (Read a, Read b) :=> Read (Either a b) where ins = Sub Dict
instance (Integral a, Read a) :=> Read (Ratio a) where ins = Sub Dict
instance () :=> Read Word where ins = Sub Dict
instance Read a :=> Read (Identity a) where ins = Sub Dict
instance Read a :=> Read (Const a b) where ins = Sub Dict
instance () :=> Read Natural where ins = Sub Dict

-- Enum
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
instance () :=> Enum Word where ins = Sub Dict
instance Enum a :=> Enum (Identity a) where ins = Sub Dict
instance Enum a :=> Enum (Const a b) where ins = Sub Dict
instance () :=> Enum Natural where ins = Sub Dict

-- Bounded
instance Class () (Bounded a) where cls = Sub Dict
instance () :=> Bounded () where ins = Sub Dict
instance () :=> Bounded Ordering where ins = Sub Dict
instance () :=> Bounded Bool where ins = Sub Dict
instance () :=> Bounded Int where ins = Sub Dict
instance () :=> Bounded Char where ins = Sub Dict
instance (Bounded a, Bounded b) :=> Bounded (a,b) where ins = Sub Dict
instance () :=> Bounded Word where ins = Sub Dict
instance Bounded a :=> Bounded (Identity a) where ins = Sub Dict
instance Bounded a :=> Bounded (Const a b) where ins = Sub Dict

-- Num
instance Class () (Num a) where cls = Sub Dict
instance () :=> Num Int where ins = Sub Dict
instance () :=> Num Integer where ins = Sub Dict
instance () :=> Num Float where ins = Sub Dict
instance () :=> Num Double where ins = Sub Dict
instance RealFloat a :=> Num (Complex a) where ins = Sub Dict
instance Integral a :=> Num (Ratio a) where ins = Sub Dict
instance () :=> Num Word where ins = Sub Dict
instance Num a :=> Num (Identity a) where ins = Sub Dict
instance Num a :=> Num (Const a b) where ins = Sub Dict
instance () :=> Num Natural where ins = Sub Dict

-- Real
instance Class (Num a, Ord a) (Real a) where cls = Sub Dict
instance () :=> Real Int where ins = Sub Dict
instance () :=> Real Integer where ins = Sub Dict
instance () :=> Real Float where ins = Sub Dict
instance () :=> Real Double where ins = Sub Dict
instance Integral a :=> Real (Ratio a) where ins = Sub Dict
instance () :=> Real Word where ins = Sub Dict
instance Real a :=> Real (Identity a) where ins = Sub Dict
instance Real a :=> Real (Const a b) where ins = Sub Dict
instance () :=> Real Natural where ins = Sub Dict

-- Integral
instance Class (Real a, Enum a) (Integral a) where cls = Sub Dict
instance () :=> Integral Int where ins = Sub Dict
instance () :=> Integral Integer where ins = Sub Dict
instance () :=> Integral Word where ins = Sub Dict
instance Integral a :=> Integral (Identity a) where ins = Sub Dict
instance Integral a :=> Integral (Const a b) where ins = Sub Dict
instance () :=> Integral Natural where ins = Sub Dict

-- Bits
instance Class (Eq a) (Bits a) where cls = Sub Dict
instance () :=> Bits Bool where ins = Sub Dict
instance () :=> Bits Int where ins = Sub Dict
instance () :=> Bits Integer where ins = Sub Dict
instance () :=> Bits Word where ins = Sub Dict
instance Bits a :=> Bits (Identity a) where ins = Sub Dict
instance Bits a :=> Bits (Const a b) where ins = Sub Dict
instance () :=> Bits Natural where ins = Sub Dict

-- Fractional
instance Class (Num a) (Fractional a) where cls = Sub Dict
instance () :=> Fractional Float where ins = Sub Dict
instance () :=> Fractional Double where ins = Sub Dict
instance RealFloat a :=> Fractional (Complex a) where ins = Sub Dict
instance Integral a :=> Fractional (Ratio a) where ins = Sub Dict
instance Fractional a :=> Fractional (Identity a) where ins = Sub Dict
instance Fractional a :=> Fractional (Const a b) where ins = Sub Dict

-- Floating
instance Class (Fractional a) (Floating a) where cls = Sub Dict
instance () :=> Floating Float where ins = Sub Dict
instance () :=> Floating Double where ins = Sub Dict
instance RealFloat a :=> Floating (Complex a) where ins = Sub Dict
instance Floating a :=> Floating (Identity a) where ins = Sub Dict
instance Floating a :=> Floating (Const a b) where ins = Sub Dict

-- RealFrac
instance Class (Real a, Fractional a) (RealFrac a) where cls = Sub Dict
instance () :=> RealFrac Float where ins = Sub Dict
instance () :=> RealFrac Double where ins = Sub Dict
instance Integral a :=> RealFrac (Ratio a) where ins = Sub Dict
instance RealFrac a :=> RealFrac (Identity a) where ins = Sub Dict
instance RealFrac a :=> RealFrac (Const a b) where ins = Sub Dict

-- RealFloat
instance Class (RealFrac a, Floating a) (RealFloat a) where cls = Sub Dict
instance () :=> RealFloat Float where ins = Sub Dict
instance () :=> RealFloat Double where ins = Sub Dict
instance RealFloat a :=> RealFloat (Identity a) where ins = Sub Dict
instance RealFloat a :=> RealFloat (Const a b) where ins = Sub Dict

-- Semigroup
instance Class () (Semigroup a) where cls = Sub Dict
instance () :=> Semigroup () where ins = Sub Dict
instance () :=> Semigroup Ordering where ins = Sub Dict
instance () :=> Semigroup [a] where ins = Sub Dict
instance Semigroup a :=> Semigroup (Maybe a) where ins = Sub Dict
instance (Semigroup a, Semigroup b) :=> Semigroup (a, b) where ins = Sub Dict
instance Semigroup a :=> Semigroup (Const a b) where ins = Sub Dict
instance Semigroup a :=> Semigroup (Identity a) where ins = Sub Dict
instance Semigroup a :=> Semigroup (IO a) where ins = Sub Dict

-- Monoid
instance Class (Semigroup a) (Monoid a) where cls = Sub Dict
instance () :=> Monoid () where ins = Sub Dict
instance () :=> Monoid Ordering where ins = Sub Dict
instance () :=> Monoid [a] where ins = Sub Dict
instance Monoid a :=> Monoid (Maybe a) where ins = Sub Dict
instance (Monoid a, Monoid b) :=> Monoid (a, b) where ins = Sub Dict
instance Monoid a :=> Monoid (Const a b) where ins = Sub Dict
instance Monoid a :=> Monoid (Identity a) where ins = Sub Dict
instance Monoid a :=> Monoid (IO a) where ins = Sub Dict

-- Functor
instance Class () (Functor f) where cls = Sub Dict
instance () :=> Functor [] where ins = Sub Dict
instance () :=> Functor Maybe where ins = Sub Dict
instance () :=> Functor (Either a) where ins = Sub Dict
instance () :=> Functor ((->) a) where ins = Sub Dict
instance () :=> Functor ((,) a) where ins = Sub Dict
instance () :=> Functor IO where ins = Sub Dict
instance Monad m :=> Functor (WrappedMonad m) where ins = Sub Dict
instance () :=> Functor Identity where ins = Sub Dict
instance () :=> Functor (Const a) where ins = Sub Dict

-- Applicative
instance Class (Functor f) (Applicative f) where cls = Sub Dict
instance () :=> Applicative [] where ins = Sub Dict
instance () :=> Applicative Maybe where ins = Sub Dict
instance () :=> Applicative (Either a) where ins = Sub Dict
instance () :=> Applicative ((->)a) where ins = Sub Dict
instance () :=> Applicative IO where ins = Sub Dict
instance Monoid a :=> Applicative ((,)a) where ins = Sub Dict
instance Monoid a :=> Applicative (Const a) where ins = Sub Dict
instance Monad m :=> Applicative (WrappedMonad m) where ins = Sub Dict

-- Alternative
instance Class (Applicative f) (Alternative f) where cls = Sub Dict
instance () :=> Alternative [] where ins = Sub Dict
instance () :=> Alternative Maybe where ins = Sub Dict
instance MonadPlus m :=> Alternative (WrappedMonad m) where ins = Sub Dict

-- Monad
instance Class (Applicative f) (Monad f) where cls = Sub Dict
instance () :=> Monad [] where ins = Sub Dict
instance () :=> Monad ((->) a) where ins = Sub Dict
instance () :=> Monad (Either a) where ins = Sub Dict
instance () :=> Monad IO where ins = Sub Dict
instance () :=> Monad Identity where ins = Sub Dict

-- MonadPlus
instance Class (Monad f, Alternative f) (MonadPlus f) where cls = Sub Dict
instance () :=> MonadPlus [] where ins = Sub Dict
instance () :=> MonadPlus Maybe where ins = Sub Dict

--------------------------------------------------------------------------------
-- UndecidableInstances
--------------------------------------------------------------------------------

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

instance () :=> Semigroup (Dict a) where ins = Sub Dict
instance Semigroup (Dict a) where
  Dict <> Dict = Dict

instance a :=> Monoid (Dict a) where ins = Sub Dict
instance a => Monoid (Dict a) where
  mempty = Dict
