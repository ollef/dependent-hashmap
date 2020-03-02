{-# language ConstraintKinds #-}
{-# language FlexibleInstances #-}
{-# language GADTs #-}
{-# language MultiParamTypeClasses #-}
{-# language StandaloneDeriving #-}
{-# language TemplateHaskell #-}
{-# language TypeFamilies #-}
module Main where

import Control.Monad
import Control.Monad.Identity
import Data.Maybe
import Data.Constraint
import Data.Constraint.Compose
import Data.Constraint.Extras
import Data.GADT.Compare
import Data.GADT.Show
import Data.Hashable
import Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import Data.Dependent.HashMap (DHashMap, DSum((:=>)), Some(Some))
import qualified Data.Dependent.HashMap as DHashMap

data Key v where
  IntKey :: Int -> Key Int
  StringKey :: String -> Key String

deriving instance Show (Key v)

instance GShow Key where
  gshowsPrec = showsPrec

instance Hashable (Some Key) where
  hashWithSalt salt (Some key) =
    case key of
      IntKey i -> hashWithSalt salt i `mod` 20
      StringKey s -> hashWithSalt salt s `mod` 20

instance GRead Key where
  greadsPrec d s =
    readParen (d > 10)
      (\s' ->
        [ (GReadResult $ \f -> f $ IntKey i, s''')
        | ("IntKey", s'') <- lex s'
        , (i, s''') <- readsPrec (10+1) s''
        ]
      )
      s
      ++
    readParen (d > 10)
      (\s' ->
        [ (GReadResult $ \f -> f $ StringKey m, s''')
        | ("StringKey", s'') <- lex s'
        , (m, s''') <- readsPrec (10+1) s''
        ]
      )
      s

instance (c (f Int), c (f String)) => ArgDict (ComposeC c f) Key where
  type ConstraintsFor Key (ComposeC c f) = ()
  argDict key =
    case key of
      IntKey {} -> Dict
      StringKey {} -> Dict

instance GEq Key where
  geq (IntKey i1) (IntKey i2)
    | i1 == i2 =
      Just Refl
  geq (StringKey s1) (StringKey s2)
    | s1 == s2 =
      Just Refl
  geq _ _ =
    Nothing

int :: Gen Int
int = Gen.int (Range.linear 0 100)

string :: Gen String
string = Gen.string (Range.linear 0 100) Gen.ascii

-- key :: Gen (Some Key)
-- key =
--   Gen.choice
--     [ Some . IntKey <$> int
--     , Some . StringKey <$> string
--     ]

dSum :: Gen (DHashMap.DSum Key Identity)
dSum =
  Gen.choice
    [ (:=>) <$> (IntKey <$> int) <*> (Identity <$> int)
    , (:=>) <$> (StringKey <$> string) <*> (Identity <$> string)
    ]

dHashMap :: Gen (DHashMap Key Identity)
dHashMap =
  DHashMap.fromList <$> Gen.list (Range.linear 0 100) dSum

prop_show_read :: Property
prop_show_read =
  property $ do
    m <- forAll dHashMap
    m === read (show m)

prop_empty :: Property
prop_empty =
  property $ do
    i <- forAll int
    DHashMap.lookup (IntKey i) (mempty :: DHashMap Key Identity) === Nothing
    s <- forAll string
    DHashMap.lookup (StringKey s) (mempty :: DHashMap Key Identity) === Nothing

prop_singleton :: Property
prop_singleton =
  property $ do
    i <- forAll int
    j <- forAll int
    DHashMap.lookup (IntKey i) (DHashMap.singleton (IntKey i) (Identity j)) === Just (Identity j)
    s <- forAll string
    DHashMap.lookup (StringKey s) (DHashMap.singleton (IntKey i) (Identity j)) === Nothing

prop_null_size :: Property
prop_null_size =
  property $ do
    h <- forAll dHashMap
    DHashMap.null h === (DHashMap.size h == 0)

prop_member_lookup :: Property
prop_member_lookup =
  property $ do
    h <- forAll dHashMap
    i <- forAll int
    isJust (DHashMap.lookup (IntKey i) h) === DHashMap.member (IntKey i) h
    s <- forAll string
    isJust (DHashMap.lookup (StringKey s) h) === DHashMap.member (StringKey s) h

prop_insert_lookup :: Property
prop_insert_lookup =
  property $ do
    h <- forAll dHashMap
    i <- forAll int
    j <- forAll int
    DHashMap.lookup (IntKey i) (DHashMap.insert (IntKey i) (Identity j) h) === Just (Identity j)
    s <- forAll string
    t <- forAll string
    DHashMap.lookup (StringKey s) (DHashMap.insert (StringKey s) (Identity t) h) === Just (Identity t)

prop_bang_lookup :: Property
prop_bang_lookup =
  property $ do
    h <- forAll dHashMap
    i <- forAll int
    j <- forAll int
    DHashMap.insert (IntKey i) (Identity j) h DHashMap.! IntKey i === Identity j
    s <- forAll string
    t <- forAll string
    DHashMap.insert (StringKey s) (Identity t) h DHashMap.! StringKey s === Identity t

prop_lookup_default :: Property
prop_lookup_default =
  property $ do
    h <- forAll dHashMap
    i <- forAll int
    j <- forAll int
    DHashMap.lookupDefault (Identity j) (IntKey i) h ===
      if DHashMap.member (IntKey i) h then
        h DHashMap.! IntKey i
      else
        Identity j

prop_lookup_delete :: Property
prop_lookup_delete =
  property $ do
    h <- forAll dHashMap
    i <- forAll int
    DHashMap.lookup (IntKey i) (DHashMap.delete (IntKey i) h) === Nothing

main :: IO ()
main =
  void $ checkParallel $$(discover)
