{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE CPP #-}
-- | Utilities for working with 'KnownChar' constraints.
--
-- This module is only available on GHC 9.2 or later.
module Data.Constraint.Char
  ( CharToNat
  , NatToChar
  , charToNat
  , natToChar
  ) where

import Data.Char
import Data.Constraint
import Data.Proxy
import GHC.TypeLits
#if MIN_VERSION_base(4,18,0)
import Data.Constraint.Unsafe
import qualified GHC.TypeNats as TN
#else
import Unsafe.Coerce
#endif

-- implementation details

#if !MIN_VERSION_base(4,18,0)
newtype Magic c = Magic (KnownChar c => Dict (KnownChar c))
#endif

magicCN :: forall c n. (Char -> Int) -> KnownChar c :- KnownNat n
#if MIN_VERSION_base(4,18,0)
magicCN f = Sub $ TN.withKnownNat (unsafeSNat @n (fromIntegral (f (charVal (Proxy @c))))) Dict
#else
magicCN f = Sub $ unsafeCoerce (Magic Dict) (fromIntegral @Int @Natural (f (charVal (Proxy @c))))
#endif

magicNC :: forall n c. (Int -> Char) -> KnownNat n :- KnownChar c
#if MIN_VERSION_base(4,18,0)
magicNC f = Sub $ withKnownChar (unsafeSChar @c (f (fromIntegral (natVal (Proxy @n))))) Dict
#else
magicNC f = Sub $ unsafeCoerce (Magic Dict) (f (fromIntegral (natVal (Proxy @n))))
#endif

-- operations

charToNat :: forall c. KnownChar c :- KnownNat (CharToNat c)
charToNat = magicCN ord

-- NB: 0x10FFFF the maximum value for a Unicode code point. Calling `chr` on
-- anything greater will throw an exception.
natToChar :: forall n. (n <= 0x10FFFF, KnownNat n) :- KnownChar (NatToChar n)
natToChar = Sub $ case magicNC @n @(NatToChar n) chr of Sub r -> r
