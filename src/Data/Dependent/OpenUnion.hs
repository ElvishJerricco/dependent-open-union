{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

{-|
Module      : Data.Dependent.OpenUnion
Description : Unions over types of kind 'k -> *'
Copyright   : 2016 Will Fancher
License     : BSD-3
Maintainer  : willfancher38@gmail.com
Stability   : experimental

This implementation relies on _closed_ type families added to GHC
7.8. It has NO overlapping instances and NO Typeable. Alas, the
absence of Typeable means the projections and injections generally
take linear time.  The code illustrate how to use closed type families
to disambiguate otherwise overlapping instances.

The data constructors of Union are not exported. Essentially, the
nested Either data type.

Using <http://okmij.org/ftp/Haskell/extensible/OpenUnion41.hs> as a
starting point.

-}

module Data.Dependent.OpenUnion
  ( Union
  , Member(..)
  , Members
  , hoistU) where

import           Data.GADT.Compare
import           Data.Proxy
import           GHC.Exts

--------------------------------------------------------------------------------
                           -- Interface --
--------------------------------------------------------------------------------
data Union r v where
  UNow  :: t v -> Union (t ': r) v
  UNext :: Union r v -> Union (any ': r) v

class (Member' t r (FindElem t r)) => Member (t :: k -> *) (r :: [ k -> * ]) where
  type Remove t r :: [ k -> * ]
  weaken :: Proxy t -> Union (Remove t r) v -> Union r v
  inj :: t v -> Union r v
  prj :: Union r v -> Either (Union (Remove t r) v) (t v)

instance (Member' t r (FindElem t r)) => Member t r where
  type Remove t r = Remove' t r (FindElem t r)
  weaken = weaken' (Proxy :: Proxy (FindElem t r))
  {-# INLINE weaken #-}
  inj = inj' (Proxy :: Proxy (FindElem t r))
  {-# INLINE inj #-}
  prj = prj' (Proxy :: Proxy (FindElem t r))
  {-# INLINE prj #-}

type family Members m r :: Constraint where
  Members (t ': c) r = (Member t r, Members c r)
  Members '[] r = ()

instance Functor (Union '[]) where
  fmap _ _ = error "Not possible - empty union"

instance (Functor t, Functor (Union r)) => Functor (Union (t ': r)) where
  fmap f u = case prj u of
    Right (ta :: t a) -> inj (fmap f ta)
    Left u' -> weaken (Proxy :: Proxy t) $ fmap f u'

hoistU :: forall t r f r' a. (Member t r, Member f r', Remove t r ~ Remove f r')
       => (t a -> f a) -> Union r a -> Union r' a
hoistU n u = case prj u of
  Right ta -> inj (n ta)
  Left u' -> weaken (Proxy :: Proxy f) u'

instance GEq (Union '[]) where
  _ `geq` _ = error "Not possible - empty union"

instance (GEq f, GEq (Union r)) => GEq (Union (f ': r)) where
  UNow fa `geq` UNow fb = fa `geq` fb
  UNext ua `geq` UNext ub = ua `geq` ub
  _ `geq` _ = Nothing

instance GCompare (Union '[]) where
  _ `gcompare` _ = error "Not possible - empty union"

instance (GCompare f, GCompare (Union r)) => GCompare (Union (f ': r)) where
  UNow fa `gcompare` UNow fb = fa `gcompare` fb
  UNow _ `gcompare` UNext _ = GLT
  UNext _ `gcompare` UNow _ = GGT
  UNext ua `gcompare` UNext ub = ua `gcompare` ub

--------------------------------------------------------------------------------
                         -- Implementation --
--------------------------------------------------------------------------------
data Nat = S Nat | Z

-- injecting/projecting at a specified position Proxy n
class Member' (t :: k -> *) (r :: [ k -> * ]) (n :: Nat) where
  type Remove' t r n :: [ k -> * ]
  weaken' :: Proxy n -> Proxy t -> Union (Remove' t r n) v -> Union r v
  inj' :: Proxy n -> t v -> Union r v
  prj' :: Proxy n -> Union r v -> Either (Union (Remove' t r n) v) (t v)

instance Member' t (t ': r') 'Z where
  type Remove' t (t ': r') 'Z = r'
  weaken' _ _ = UNext
  inj' _ = UNow
  prj' _ (UNow x)  = Right x
  prj' _ (UNext u) = Left u

instance (Member' t r' n) => Member' t (t' ': r') ('S n) where
  type Remove' t (t' ': r') ('S n) = t' ': (Remove' t r' n)
  weaken' _ _ (UNow x)  = UNow x
  weaken' _ _ (UNext u) = UNext $ weaken' (Proxy::Proxy n) (Proxy::Proxy t) u
  inj' _ = UNext . inj' (Proxy::Proxy n)
  prj' _ (UNow x)  = Left $ UNow x
  prj' _ (UNext x) = case prj' (Proxy::Proxy n) x of
    Right x' -> Right x'
    Left u   -> Left $ UNext u

-- Find an index of an element in a `list'
-- The element must exist
-- This closed type family disambiguates otherwise overlapping
-- instances
type family FindElem (t :: k -> *) r :: Nat where
  FindElem t (t ': r)    = 'Z
  FindElem t (any ': r)  = 'S (FindElem t r)
