{-# language FlexibleContexts #-}
{-# language GADTs #-}
{-# language GeneralizedNewtypeDeriving #-}
{-# language RankNTypes #-}
{-# language StandaloneDeriving #-}
{-# language TypeFamilies #-}
{-# language UndecidableInstances #-}

-- | A map from hashable keys to values where the keys can specify the type of
-- value that is associated with them. A map cannot contain duplicate keys;
-- each key can map to at most one value. A 'DHashMap' makes no guarantees as to
-- the order of its elements.
--
-- The interface mirrors that of 'HashMap', with small adjustments and
-- additions.  The implementation is a thin layer on top of 'HashMap'.
--
-- The implementation is based on /hash array mapped tries/.  A
-- 'DHashMap' is often faster than other tree-based set types,
-- especially when key comparison is expensive, as in the case of
-- strings.
--
-- Many operations have a average-case complexity of /O(log n)/.  The
-- implementation uses a large base (i.e. 16) so in practice these
-- operations are constant time.
module Data.Dependent.HashMap
  ( DHashMap
  -- * Construction
  , empty
  , singleton
  -- * Basic interface
  , null
  , size
  , member
  , lookup
  , lookupDefault
  , (!)
  , insert
  , insertWith
  , delete
  , adjust
  , update
  , alter
  , alterF
  , alterLookup
  -- * Union
  , union
  , unionWith
  , unionWithKey
  , unions
  , unionsWith
  , unionsWithKey
  -- * Transformations
  , map
  , mapWithKey
  , traverse
  , traverseWithKey
  -- * Difference and intersection
  , difference
  , differenceWith
  , differenceWithKey
  , intersection
  , intersectionWith
  , intersectionWithKey
  -- * Folds
  , foldMap
  , foldMapWithKey
  , foldl
  , foldlWithKey
  , foldl'
  , foldlWithKey'
  , foldr
  , foldrWithKey
  -- * Filter
  , filter
  , filterWithKey
  , mapMaybe
  , mapMaybeWithKey
  -- * Conversions
  , keys
  , elems
  -- * Lists
  , toList
  , fromList
  , fromListWith
  , fromListWithKey
  -- * Re-exports
  , DSum ((:=>))
  , Some (Some)
  )
  where

import Prelude hiding (lookup, null, map, traverse, foldMap, foldl, foldr, filter)
import qualified Prelude

import Data.Constraint.Extras
import Data.Dependent.Sum
import qualified Data.Foldable as Foldable
import Data.GADT.Compare
import Data.GADT.Show
import Data.Hashable
import qualified Data.HashMap.Lazy as HashMap
import Data.Some
import GHC.Exts (IsList(Item))
import qualified GHC.Exts
import Text.Read

-- | A map from keys @k@ to values @v@ where @k@ and @v@ are indexed types and
-- where every key-value pair is indexed by the same type.
newtype DHashMap k v =
  DHashMap (HashMap.HashMap (Some k) (DSum k v))

-------------------------------------------------------------------------------
-- Instances

deriving instance (GEq k, Has' Eq k v) => Eq (DHashMap k v)
deriving instance (GCompare k, Has' Eq k v, Has' Ord k v) => Ord (DHashMap k v)
deriving instance (GEq k, Hashable (Some k)) => Semigroup (DHashMap k v)
deriving instance (GEq k, Hashable (Some k)) => Monoid (DHashMap k v)

instance (GEq k, Hashable (Some k)) => IsList (DHashMap k v) where
  type Item (DHashMap k v) = DSum k v
  fromList =
    Data.Dependent.HashMap.fromList

  toList =
    Data.Dependent.HashMap.toList

instance (GEq k, GRead k, Has' Read k v, Hashable (Some k)) => Read (DHashMap k v) where
  readPrec =
    parens $ prec 10 $ do
      Ident "fromList" <- lexP
      xs <- readPrec
      return (fromList xs)

  readListPrec = readListPrecDefault

instance (GShow k, Has' Show k v) => Show (DHashMap k v) where
  showsPrec p m =
    showParen (p > 10) $
      showString "fromList " .
      showsPrec 11 (Data.Dependent.HashMap.toList m)

-------------------------------------------------------------------------------
-- * Construction

-- | /O(1)/ Construct an empty map.
empty :: DHashMap k v
empty =
  DHashMap HashMap.empty

-- | /O(1)/ Construct a map with a single element.
singleton
  :: Hashable (Some k)
  => k a
  -> v a
  -> DHashMap k v
singleton k v =
  DHashMap $ HashMap.singleton (Some k) (k :=> v)

-------------------------------------------------------------------------------
-- * Basic interface

-- | /O(1)/ Return 'True' if this map is empty, 'False' otherwise.
null :: DHashMap k v -> Bool
null (DHashMap h) =
  HashMap.null h

-- | /O(n)/ Return the number of key-value mappings in this map.
size :: DHashMap k v -> Int
size (DHashMap h) =
  HashMap.size h

-- | /O(log n)/ Return 'True' if the specified key is present in the
-- map, 'False' otherwise.
member
  :: (GEq k, Hashable (Some k))
  => k a
  -> DHashMap k v
  -> Bool
member k (DHashMap h) =
  HashMap.member (Some k) h

-- | /O(log n)/ Return the value to which the specified key is mapped,
-- or 'Nothing' if this map contains no mapping for the key.
lookup
  :: (GEq k, Hashable (Some k))
  => k a
  -> DHashMap k v
  -> Maybe (v a)
lookup k (DHashMap h) =
  case HashMap.lookup (Some k) h of
    Just (k' :=> v)
      | Just Refl <- geq k k' ->
        Just v
    _ ->
      Nothing

-- | /O(log n)/ Return the value to which the specified key is mapped,
-- or the default value if this map contains no mapping for the key.
lookupDefault
  :: (GEq k, Hashable (Some k))
  => v a
  -> k a
  -> DHashMap k v
  -> v a
lookupDefault default_ k (DHashMap h) =
  case HashMap.lookupDefault (k :=> default_) (Some k) h of
    k' :=> v
      | Just Refl <- geq k k' ->
        v
      | otherwise ->
        error "Data.Dependent.HashMap.lookupDefault: key mismatch"

-- | /O(log n)/ Return the value to which the specified key is mapped.
-- Calls 'error' if this map contains no mapping for the key.
(!)
  :: (GEq k, Hashable (Some k))
  => DHashMap k v
  -> k a
  -> v a
DHashMap h ! k =
  case h HashMap.! Some k of
    k' :=> v
      | Just Refl <- geq k k' ->
        v
      | otherwise ->
        error "Data.Dependent.HashMap.(!): key mismatch"

-- | /O(log n)/ Associate the specified value with the specified
-- key in this map.  If this map previously contained a mapping for
-- the key, the old value is replaced.
insert
  :: (GEq k, Hashable (Some k))
  => k a
  -> v a
  -> DHashMap k v
  -> DHashMap k v
insert k v (DHashMap h) =
  DHashMap $ HashMap.insert (Some k) (k :=> v) h

-- | /O(log n)/ Associate the value with the key in this map.  If
-- this map previously contained a mapping for the key, the old value
-- is replaced by the result of applying the given function to the new
-- and old value.  Example:
--
-- > insertWith f k v map
-- >   where f new old = new + old
insertWith
  :: (GEq k, Hashable (Some k))
  => (v a -> v a -> v a)
  -> k a
  -> v a
  -> DHashMap k v
  -> DHashMap k v
insertWith f k v (DHashMap h) =
  DHashMap $
    HashMap.insertWith
      (\(k1 :=> v1) (k2 :=> v2) ->
        case (geq k k1, geq k k2) of
          (Just Refl, Just Refl) ->
            k :=> f v1 v2
          _ ->
            error "Data.Dependent.HashMap.insertWith: key mismatch"
      )
      (Some k)
      (k :=> v)
      h

-- | /O(log n)/ Remove the mapping for the specified key from this map
-- if present.
delete
  :: (GEq k, Hashable (Some k))
  => k a
  -> DHashMap k v
  -> DHashMap k v
delete k (DHashMap h) =
  DHashMap $ HashMap.delete (Some k) h

-- | /O(log n)/ Adjust the value tied to a given key in this map only
-- if it is present. Otherwise, leave the map alone.
adjust
  :: (GEq k, Hashable (Some k))
  => (v a -> v a)
  -> k a
  -> DHashMap k v
  -> DHashMap k v
adjust f k (DHashMap h) =
  DHashMap $
    HashMap.adjust
      (\(k' :=> v) ->
        case geq k k' of
          Just Refl ->
            k :=> f v
          _ ->
            error "Data.Dependent.HashMap.adjust: key mismatch"
      )
      (Some k)
      h

-- | /O(log n)/  The expression (@'update' f k map@) updates the value @x@ at @k@,
-- (if it is in the map). If (f k x) is @'Nothing', the element is deleted.
-- If it is (@'Just' y), the key k is bound to the new value y.
update
  :: (GEq k, Hashable (Some k))
  => (v a -> Maybe (v a))
  -> k a
  -> DHashMap k v
  -> DHashMap k v
update f k (DHashMap h) =
  DHashMap $
    HashMap.update
      (\(k' :=> v) ->
        case geq k k' of
          Just Refl ->
            (k :=>) <$> f v
          _ ->
            error "Data.Dependent.HashMap.update: key mismatch"
      )
      (Some k)
      h

-- | /O(log n)/  The expression (@'alter' f k map@) alters the value @x@ at @k@, or
-- absence thereof. @alter@ can be used to insert, delete, or update a value in a
-- map. In short : @'lookup' k ('alter' f k m) = f ('lookup' k m)@.
alter
  :: (GEq k, Hashable (Some k))
  => (Maybe (v a) -> Maybe (v a))
  -> k a
  -> DHashMap k v
  -> DHashMap k v
alter f k (DHashMap h) =
  DHashMap $
    HashMap.alter
      (\kv ->
        (k :=>) <$>
        case kv of
          Just (k' :=> v)
            | Just Refl <- geq k k' ->
              f (Just v)
          _ ->
            f Nothing
      )
      (Some k)
      h

-- | /O(log n)/  The expression (@'alterF' f k map@) alters the value @x@ at
-- @k@, or absence thereof. @alterF@ can be used to insert, delete, or update
-- a value in a map.
alterF
  :: (Functor f, GEq k, Hashable (Some k))
  => (Maybe (v a) -> f (Maybe (v a)))
  -> k a
  -> DHashMap k v
  -> f (DHashMap k v)
alterF f k (DHashMap h) =
  DHashMap <$>
    HashMap.alterF
      (\mkv ->
        fmap (k :=>) <$>
        case mkv of
          Just (k' :=> v)
            | Just Refl <- geq k k' ->
              f (Just v)

          _ ->
            f Nothing
      )
      (Some k)
      h

-- | /O(log n)/  @'alterLookup' f k map@ looks up the value at @k@, if any,
-- and 'alter's it, in one operation.
--
-- @'alterLookup' f k map = ('lookup' k map, 'alter' f k map)@
alterLookup
  :: (GEq k, Hashable (Some k))
  => (Maybe (v a) -> Maybe (v a))
  -> k a
  -> DHashMap k v
  -> (Maybe (v a), DHashMap k v)
alterLookup f k =
  alterF (\mv' -> (mv', f mv')) k

-------------------------------------------------------------------------------
-- * Union

-- | /O(n+m)/ The union of two maps. If a key occurs in both maps, the
-- mapping from the first will be the mapping in the result.
union
  :: (GEq k, Hashable (Some k))
  => DHashMap k v
  -> DHashMap k v
  -> DHashMap k v
union = (<>)

-- | /O(n+m)/ The union of two maps.  If a key occurs in both maps,
-- the provided function (first argument) will be used to compute the
-- result.
unionWith
  :: (GEq k, Hashable (Some k))
  => (forall a. v a -> v a -> v a)
  -> DHashMap k v
  -> DHashMap k v
  -> DHashMap k v
unionWith f (DHashMap h1) (DHashMap h2) =
  DHashMap $
    HashMap.unionWith
      (\(k1 :=> v1) (k2 :=> v2) ->
        case geq k1 k2 of
          Just Refl ->
            k1 :=> f v1 v2
          _ ->
            error "Data.Dependent.HashMap.unionWith: key mismatch"
      )
      h1
      h2

-- | /O(n+m)/ The union of two maps.  If a key occurs in both maps,
-- the provided function (first argument) will be used to compute the
-- result.
unionWithKey
  :: (GEq k, Hashable (Some k))
  => (forall a. k a -> v a -> v a -> v a)
  -> DHashMap k v
  -> DHashMap k v
  -> DHashMap k v
unionWithKey f (DHashMap h1) (DHashMap h2) =
  DHashMap $
    HashMap.unionWith
      (\(k1 :=> v1) (k2 :=> v2) ->
        case geq k1 k2 of
          Just Refl ->
            k1 :=> f k1 v1 v2
          _ ->
            error "Data.Dependent.HashMap.unionWithKey: key mismatch"
      )
      h1
      h2

-- | The union of a list of maps.
unions
  :: (GEq k, Hashable (Some k), Foldable f)
  => f (DHashMap k v)
  -> DHashMap k v
unions =
  Foldable.foldl' union empty

-- | The union of a list of maps, with combining operation.
unionsWith
  :: (GEq k, Hashable (Some k), Foldable f)
  => (forall a. v a -> v a -> v a)
  -> f (DHashMap k v)
  -> DHashMap k v
unionsWith f =
  Foldable.foldl' (unionWith f) empty

-- | The union of a list of maps, with combining operation.
unionsWithKey
  :: (GEq k, Hashable (Some k), Foldable f)
  => (forall a. k a -> v a -> v a -> v a)
  -> f (DHashMap k v)
  -> DHashMap k v
unionsWithKey f =
  Foldable.foldl' (unionWithKey f) empty

-------------------------------------------------------------------------------
-- * Transformations

-- | /O(n)/ Transform this map by applying a function to every value.
map :: (forall a. v a -> v' a) -> DHashMap k v -> DHashMap k v'
map f (DHashMap h) =
  DHashMap $ HashMap.map (\(k :=> v) -> (k :=> f v)) h

-- | /O(n)/ Transform this map by applying a function to every value.
mapWithKey :: (forall a. k a -> v a -> v' a) -> DHashMap k v -> DHashMap k v'
mapWithKey f (DHashMap h) =
  DHashMap $ HashMap.map (\(k :=> v) -> (k :=> f k v)) h

-- | /O(n)/ Perform an 'Applicative' action for each value
-- in a map and produce a map of all the results.
--
-- Note: the order in which the actions occur is unspecified. In particular,
-- when the map contains hash collisions, the order in which the actions
-- associated with the keys involved will depend in an unspecified way on
-- their insertion order.
traverse
  :: Applicative f
  => (forall a. v a -> f (v' a))
  -> DHashMap k v
  -> f (DHashMap k v')
traverse f (DHashMap h) =
  DHashMap <$>
    Prelude.traverse (\(k :=> v) -> (k :=>) <$> f v) h

-- | /O(n)/ Perform an 'Applicative' action for each key-value pair
-- in a map and produce a map of all the results.
--
-- Note: the order in which the actions occur is unspecified. In particular,
-- when the map contains hash collisions, the order in which the actions
-- associated with the keys involved will depend in an unspecified way on
-- their insertion order.
traverseWithKey
  :: Applicative f
  => (forall a. k a -> v a -> f (v' a))
  -> DHashMap k v
  -> f (DHashMap k v')
traverseWithKey f (DHashMap h) =
  DHashMap <$>
    Prelude.traverse (\(k :=> v) -> (k :=>) <$> f k v) h

-------------------------------------------------------------------------------
-- * Difference and intersection

-- | /O(n*log m)/ Difference of two maps. Return elements of the first map
-- not existing in the second.
difference
  :: (GEq k, Hashable (Some k))
  => DHashMap k v
  -> DHashMap k v'
  -> DHashMap k v
difference (DHashMap h1) (DHashMap h2) =
  DHashMap $ HashMap.difference h1 h2

-- | /O(n*log m)/ Difference with a combining function. When two equal keys are
-- encountered, the combining function is applied to the values of these keys.
-- If it returns 'Nothing', the element is discarded (proper set difference). If
-- it returns (@'Just' y@), the element is updated with a new value @y@.
differenceWith
  :: (GEq k, Hashable (Some k))
  => (forall a. v a -> v' a -> Maybe (v a))
  -> DHashMap k v
  -> DHashMap k v'
  -> DHashMap k v
differenceWith f (DHashMap h1) (DHashMap h2) =
  DHashMap $
    HashMap.differenceWith
      (\(k1 :=> v1) (k2 :=> v2) ->
        case geq k1 k2 of
          Just Refl ->
            (k1 :=>) <$> f v1 v2
          Nothing ->
            error "Data.Dependent.HashMap.differenceWith: key mismatch"
      )
      h1
      h2

-- | /O(n*log m)/ Difference with a combining function. When two equal keys are
-- encountered, the combining function is applied to the key and the values of these keys.
-- If it returns 'Nothing', the element is discarded (proper set difference). If
-- it returns (@'Just' y@), the element is updated with a new value @y@.
differenceWithKey
  :: (GEq k, Hashable (Some k))
  => (forall a. k a -> v a -> v' a -> Maybe (v a))
  -> DHashMap k v
  -> DHashMap k v'
  -> DHashMap k v
differenceWithKey f (DHashMap h1) (DHashMap h2) =
  DHashMap $
    HashMap.differenceWith
      (\(k1 :=> v1) (k2 :=> v2) ->
        case geq k1 k2 of
          Just Refl ->
            (k1 :=>) <$> f k1 v1 v2
          Nothing ->
            error "Data.Dependent.HashMap.differenceWithKey: key mismatch"
      )
      h1
      h2

-- | /O(n*log m)/ Intersection of two maps. Return elements of the first
-- map for keys existing in the second.
intersection :: (GEq k, Hashable (Some k)) => DHashMap k v -> DHashMap k v' -> DHashMap k v
intersection (DHashMap h1) (DHashMap h2) =
  DHashMap $ HashMap.intersection h1 h2

-- | /O(n+m)/ Intersection of two maps. If a key occurs in both maps
-- the provided function is used to combine the values from the two
-- maps.
intersectionWith
  :: (GEq k, Hashable (Some k))
  => (forall a. v1 a -> v2 a -> v3 a)
  -> DHashMap k v1
  -> DHashMap k v2
  -> DHashMap k v3
intersectionWith f (DHashMap h1) (DHashMap h2) =
  DHashMap $
    HashMap.intersectionWith
      (\(k1 :=> v1) (k2 :=> v2) ->
        case geq k1 k2 of
          Just Refl ->
            k1 :=> f v1 v2
          Nothing ->
            error "Data.Dependent.HashMap.intersectionWith: key mismatch"
      )
      h1
      h2

-- | /O(n+m)/ Intersection of two maps. If a key occurs in both maps
-- the provided function is used to combine the values from the two
-- maps.
intersectionWithKey
  :: (GEq k, Hashable (Some k))
  => (forall a. k a -> v1 a -> v2 a -> v3 a)
  -> DHashMap k v1
  -> DHashMap k v2
  -> DHashMap k v3
intersectionWithKey f (DHashMap h1) (DHashMap h2) =
  DHashMap $
    HashMap.intersectionWith
      (\(k1 :=> v1) (k2 :=> v2) ->
        case geq k1 k2 of
          Just Refl ->
            k1 :=> f k1 v1 v2
          Nothing ->
            error "Data.Dependent.HashMap.intersectionWithKey: key mismatch"
      )
      h1
      h2

-------------------------------------------------------------------------------
-- * Folds

-- | Map each value of the map to a monoid, and combine the results.
foldMap :: Monoid m => (forall a. v a -> m) -> DHashMap k v -> m
foldMap f (DHashMap h) =
  Prelude.foldMap (\(_ :=> v) -> f v) h

-- | Map each key-value pair of the map to a monoid, and combine the results.
foldMapWithKey :: Monoid m => (forall a. k a -> v a -> m) -> DHashMap k v -> m
foldMapWithKey f (DHashMap h) =
  Prelude.foldMap (\(k :=> v) -> f k v) h

-- | /O(n)/ Reduce this map by applying a binary operator to all
-- elements, using the given starting value (typically the
-- left-identity of the operator).
foldl :: (forall a. b -> v a -> b) -> b -> DHashMap k v -> b
foldl f base (DHashMap h) =
  Prelude.foldl (\b (_ :=> v) -> f b v) base h

-- | /O(n)/ Reduce this map by applying a binary operator to all
-- key-value pairs, using the given starting value (typically the
-- left-identity of the operator).
foldlWithKey :: (forall a. b -> k a -> v a -> b) -> b -> DHashMap k v -> b
foldlWithKey f base (DHashMap h) =
  Prelude.foldl (\b (k :=> v) -> f b k v) base h

-- | /O(n)/ Reduce this map by applying a binary operator to all
-- elements, using the given starting value (typically the
-- left-identity of the operator).  Each application of the operator
-- is evaluated before using the result in the next application.
-- This function is strict in the starting value.
foldl' :: (forall a. b -> v a -> b) -> b -> DHashMap k v -> b
foldl' f base (DHashMap h) =
  HashMap.foldl' (\b (_ :=> v) -> f b v) base h

-- | /O(n)/ Reduce this map by applying a binary operator to all
-- key-value pairs, using the given starting value (typically the
-- left-identity of the operator).  Each application of the operator
-- is evaluated before using the result in the next application.
-- This function is strict in the starting value.
foldlWithKey' :: (forall a. b -> k a -> v a -> b) -> b -> DHashMap k v -> b
foldlWithKey' f base (DHashMap h) =
  HashMap.foldl' (\b (k :=> v) -> f b k v) base h

-- | /O(n)/ Reduce this map by applying a binary operator to all
-- elements, using the given starting value (typically the
-- right-identity of the operator).
foldr :: (forall a. v a -> b -> b) -> b -> DHashMap k v -> b
foldr f base (DHashMap h) =
  HashMap.foldr (\(_ :=> v) -> f v) base h

-- | /O(n)/ Reduce this map by applying a binary operator to all
-- key-value pairs, using the given starting value (typically the
-- right-identity of the operator).
foldrWithKey :: (forall a. k a -> v a -> b -> b) -> b -> DHashMap k v -> b
foldrWithKey f base (DHashMap h) =
  HashMap.foldr (\(k :=> v) -> f k v) base h

-------------------------------------------------------------------------------
-- * Filter

-- | /O(n)/ Filter this map by retaining values that satisfy a predicate.
filter :: (forall a. v a -> Bool) -> DHashMap k v -> DHashMap k v
filter p (DHashMap h) =
  DHashMap $ HashMap.filter (\(_ :=> v) -> p v) h

-- | /O(n)/ Filter this map by retaining only key-value pairs satisfying a
-- predicate.
filterWithKey :: (forall a. k a -> v a -> Bool) -> DHashMap k v -> DHashMap k v
filterWithKey p (DHashMap h) =
  DHashMap $ HashMap.filter (\(k :=> v) -> p k v) h

-- | /O(n)/ Transform this map by applying a function to every value
--   and retaining only the 'Just' results.
mapMaybe :: (forall a. v1 a -> Maybe (v2 a)) -> DHashMap k v1 -> DHashMap k v2
mapMaybe f (DHashMap h) =
  DHashMap $ HashMap.mapMaybe (\(k :=> v) -> (k :=>) <$> f v) h

-- | /O(n)/ Transform this map by applying a function to every key-value pair
--   and retaining only the 'Just' results.
mapMaybeWithKey
  :: (forall a. k a -> v1 a -> Maybe (v2 a))
  -> DHashMap k v1
  -> DHashMap k v2
mapMaybeWithKey f (DHashMap h) =
  DHashMap $ HashMap.mapMaybe (\(k :=> v) -> (k :=>) <$> f k v) h

-------------------------------------------------------------------------------
-- * Conversions

-- | /O(n)/ Return a list of this map's keys.  The list is produced
-- lazily.
keys :: DHashMap k v -> [Some k]
keys (DHashMap h) =
  HashMap.keys h

-- | /O(n)/ Return a list of this map's values.  The list is produced
-- lazily.
elems :: DHashMap k v -> [Some v]
elems (DHashMap h) =
  [ Some v
  | _ :=> v <- HashMap.elems h
  ]

-------------------------------------------------------------------------------
-- * Lists

-- | /O(n)/ Return a list of this map's elements.  The list is
-- produced lazily. The order of its elements is unspecified.
toList :: DHashMap k v -> [DSum k v]
toList (DHashMap h) =
  HashMap.elems h

-- | /O(n)/ Construct a map with the supplied mappings.  If the list
-- contains duplicate mappings, the later mappings take precedence.
fromList :: (GEq k, Hashable (Some k)) => [DSum k f] -> DHashMap k f
fromList xs =
  DHashMap $
    HashMap.fromList
      [ (Some k, kv)
      | kv@(k :=> _) <- xs
      ]

-- | /O(n*log n)/ Construct a map from a list of elements.  Uses
-- the provided function to merge duplicate entries.
fromListWith
  :: (GEq k, Hashable (Some k))
  => (forall a. v a -> v a -> v a)
  -> [DSum k v]
  -> DHashMap k v
fromListWith f xs =
  DHashMap $
    HashMap.fromListWith
      (\(k1 :=> v1) (k2 :=> v2) ->
        case geq k1 k2 of
          Just Refl ->
            k1 :=> f v1 v2
          Nothing ->
            error "Data.Dependent.HashMap.fromListWith: key mismatch"
      )
      [ (Some k, kv)
      | kv@(k :=> _) <- xs
      ]

-- | /O(n*log n)/ Construct a map from a list of elements.  Uses
-- the provided function to merge duplicate entries.
fromListWithKey
  :: (GEq k, Hashable (Some k))
  => (forall a. k a -> v a -> v a -> v a)
  -> [DSum k v]
  -> DHashMap k v
fromListWithKey f xs =
  DHashMap $
    HashMap.fromListWith
      (\(k1 :=> v1) (k2 :=> v2) ->
        case geq k1 k2 of
          Just Refl ->
            k1 :=> f k1 v1 v2
          Nothing ->
            error "Data.Dependent.HashMap.fromListWithKey: key mismatch"
      )
      [ (Some k, kv)
      | kv@(k :=> _) <- xs
      ]
