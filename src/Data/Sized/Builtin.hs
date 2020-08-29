{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE TypeOperators, NoImplicitPrelude #-}
{-# LANGUAGE CPP, DataKinds, GADTs, KindSignatures, MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms, PolyKinds, RankNTypes, TypeInType           #-}
{-# LANGUAGE ViewPatterns                                                 #-}
{-# LANGUAGE NoStarIsType #-}
-- | This module exports @'S.Sized'@ type and
--   functions specialized to
--   GHC's built-in type numeral @'Nat'@.
module Data.Sized.Builtin
       ( -- * Main Data-types
    Sized(), SomeSized, pattern SomeSized, Ordinal,
    DomC(),
    -- * Accessors
    -- ** Length information
    length, sLength, null,
    -- ** Indexing
    (!!), (%!!), index, sIndex, head, last,
    uncons, uncons', Uncons, pattern Uncons,
    unsnoc, unsnoc', Unsnoc, pattern Unsnoc,
    -- ** Slicing
    tail, init, take, takeAtMost, drop, splitAt, splitAtMost,
    -- * Construction
    -- ** Initialisation
    empty, singleton, toSomeSized, replicate, replicate', generate,
    -- ** Concatenation
    cons, (<|), snoc, (|>), append, (++), concat,
    -- ** Zips
    zip, zipSame, zipWith, zipWithSame, unzip, unzipWith,
    -- * Transformation
    map, reverse, intersperse, nub, sort, sortBy, insert, insertBy,
    -- * Conversion
    -- ** List
    toList, fromList, fromList', unsafeFromList, unsafeFromList',
    fromListWithDefault, fromListWithDefault',
    -- ** Base container
    unsized,
    toSized, toSized', unsafeToSized, unsafeToSized',
    toSizedWithDefault, toSizedWithDefault',
    -- * Querying
    -- ** Partitioning
    Partitioned(), pattern Partitioned,
    takeWhile, dropWhile, span, break, partition,
    -- ** Searching
    elem, notElem, find, findIndex, sFindIndex, 
    findIndices, sFindIndices,
    elemIndex, sElemIndex, sUnsafeElemIndex, elemIndices, sElemIndices,
    -- * Views and Patterns
    -- $ViewsAndPatterns

    -- ** Views
    -- $views

    -- ** Patterns
    -- $patterns

    -- ** Definitions
    viewCons, ConsView,
    pattern (S.:-), pattern S.NilCV,
    viewSnoc, SnocView,
    pattern (S.:-::), pattern S.NilSV,

    pattern (:<), pattern NilL , pattern (:>), pattern NilR,
  ) where
import qualified Data.Sized as S
import Data.Sized (DomC)

import           Control.Subcategory
import           Data.Kind                    (Type)
import           Data.Singletons.Prelude      (SingI)
import           Data.Singletons.Prelude.Enum (PEnum (..))
import qualified Data.Type.Ordinal            as O
import GHC.TypeNats (KnownNat, Nat) 
import Prelude (Maybe, Ordering, Ord, Eq, Monoid, Bool(..), Int)
import Data.Singletons.TypeLits (SNat)
import Data.Singletons.Prelude (POrd((<=)))
import Data.Type.Natural.Class (type (-.), type (<))
import Data.Type.Natural (Min, type (-), type (+), type (*))

type Ordinal = (O.Ordinal :: Nat -> Type)
type Sized = (S.Sized :: (Type -> Type) -> Nat -> Type -> Type)

type SomeSized f a = S.SomeSized' f Nat a

pattern SomeSized
  :: forall (f :: Type -> Type) a. ()
  => forall (n :: Nat). SNat n
  -> Sized f n a -> SomeSized f a
{-# COMPLETE SomeSized #-}
pattern SomeSized n s = S.SomeSized'  n s

length :: (Dom f a, CFoldable f, KnownNat n) => Sized f n a -> Int
length = S.length @Nat

sLength :: (Dom f a, CFoldable f) => Sized f n a -> SNat n
sLength = S.sLength @Nat

null :: (Dom f a, CFoldable f) => Sized f n a -> Bool
null = S.null @Nat

(!!) :: (Dom f a, CFoldable f, (1 <= m) ~ 'True) => Sized f m a -> Int -> a
(!!) = (S.!!) @Nat

(%!!) :: (Dom f c, CFoldable f) => Sized f n c -> Ordinal n -> c
(%!!) = (S.%!!) @Nat

index
  :: (Dom f a, CFoldable f, (1 <= m) ~ 'True)
  => Int -> Sized f m a -> a
index = S.index @Nat

sIndex :: (Dom f c, CFoldable f) => Ordinal n -> Sized f n c -> c
sIndex = S.sIndex @Nat

head :: (Dom f a, CFoldable f, (0 < n) ~ 'True) => Sized f n a -> a
head = S.head @Nat

last :: (Dom f a, CFoldable f, (0 < n) ~ 'True) => Sized f n a -> a
last = S.last @Nat

uncons
  :: (Dom f a, KnownNat n, CFreeMonoid f, (0 < n) ~ 'True)
  => Sized f n a -> Uncons f n a
uncons = S.uncons @Nat

uncons'
  :: (Dom f a, KnownNat n, CFreeMonoid f, (0 < n) ~ 'True)
  => Sized f n a
  -> Uncons f n a
uncons' = S.uncons @Nat

unsnoc
  :: (Dom f a, KnownNat n, CFreeMonoid f, (0 < n) ~ 'True)
  => Sized f n a -> Unsnoc f n a
unsnoc = S.unsnoc @Nat

unsnoc' :: (Dom f a, KnownNat n, CFreeMonoid f) => proxy n -> Sized f (n + 1) a -> Unsnoc f (n + 1) a
unsnoc' = S.unsnoc' @Nat

type Uncons f (n :: Nat) a = S.Uncons f n a
pattern Uncons
  :: forall (f :: Type -> Type) (n :: Nat) a. ()
  => forall (n1 :: Nat). (n ~ Succ n1, SingI n1)
  => a -> Sized f n1 a -> Uncons f n a
pattern Uncons a as = S.Uncons a as

type Unsnoc f (n :: Nat) a = S.Unsnoc f n a

pattern Unsnoc
  :: forall (f :: Type -> Type) (n :: Nat) a. ()
  => forall (n1 :: Nat). (n ~ Succ n1)
  => Sized f n1 a -> a -> Unsnoc f n a
pattern Unsnoc xs x = S.Unsnoc xs x

tail :: (Dom f a, CFreeMonoid f) => Sized f (1 + n) a -> Sized f n a
tail = S.tail @Nat

init :: (Dom f a, CFreeMonoid f) => Sized f (n + 1) a -> Sized f n a
init = S.init @Nat

take
  :: (Dom f a, CFreeMonoid f, (n <= m) ~ 'True)
  => SNat n -> Sized f m a -> Sized f n a
take = S.take @Nat

takeAtMost
  :: (Dom f a, CFreeMonoid f)
  => SNat n -> Sized f m a -> Sized f (Min n m) a
takeAtMost = S.takeAtMost @Nat

drop
  :: (Dom f a, CFreeMonoid f, (n <= m) ~ 'True)
  => SNat n -> Sized f m a -> Sized f (m - n) a
drop = S.drop @Nat

splitAt
  :: (Dom f a, CFreeMonoid f, (n <= m) ~ 'True)
  => SNat n -> Sized f m a -> (Sized f n a, Sized f (m - n) a)
splitAt = S.splitAt @Nat

splitAtMost
  :: (Dom f a, CFreeMonoid f)
  => SNat n -> Sized f m a
  -> (Sized f (Min n m) a, Sized f (m -. n) a)
splitAtMost = S.splitAtMost @Nat

empty :: (Dom f a, Monoid (f a)) => Sized f 0 a
empty = S.empty @Nat

singleton :: (Dom f a, CFreeMonoid f) => a -> Sized f 1 a
singleton = S.singleton @Nat

toSomeSized :: (Dom f a, CFoldable f) => f a -> SomeSized f a
toSomeSized = S.toSomeSized @Nat

replicate :: (Dom f a, CFreeMonoid f) => SNat n -> a -> Sized f n a
replicate = S.replicate @Nat

replicate' :: (Dom f a, CFreeMonoid f) => SNat n -> a -> Sized f n a
replicate' = S.replicate @Nat

generate :: (Dom f a, CFreeMonoid f, KnownNat n) => SNat n -> (Ordinal n -> a) -> Sized f n a
generate = S.generate @Nat

cons :: (Dom f a, CFreeMonoid f) => a -> Sized f n a -> Sized f (n + 1) a
cons = S.cons @Nat

snoc :: (Dom f a, CFreeMonoid f) => Sized f n a -> a -> Sized f (n + 1) a
snoc = S.snoc @Nat

(<|) :: (Dom f a, CFreeMonoid f) => a -> Sized f n a -> Sized f (n + 1) a
(<|) = (S.<|) @Nat

(|>) :: (Dom f a, CFreeMonoid f) => Sized f n a -> a -> Sized f (n + 1) a
(|>) = (S.|>) @Nat

(++) :: (Dom f a, CFreeMonoid f) => Sized f n a -> Sized f m a -> Sized f (n + m) a
(++) = (S.++) @Nat

append :: (Dom f a, CFreeMonoid f) => Sized f n a -> Sized f m a -> Sized f (n + m) a
append = S.append @Nat

concat
  :: (Dom f a, Dom f' (f a), Dom f' (Sized f n a),
      CFreeMonoid f, CFunctor f', CFoldable f'
    ) => Sized f' m (Sized f n a) -> Sized f (m * n) a
concat = S.concat @Nat

zip :: (Dom f a, Dom f b, Dom f (a, b), CZip f)
  => Sized f n a -> Sized f m b -> Sized f (Min n m) (a, b)
zip = S.zip @Nat

zipSame :: (Dom f a, Dom f b, Dom f (a, b), CZip f)
  => Sized f n a -> Sized f n b -> Sized f n (a, b)
zipSame = S.zipSame @Nat

zipWith :: (Dom f a, Dom f b, Dom f c, CZip f, CFreeMonoid f)
  => (a -> b -> c) -> Sized f n a -> Sized f m b -> Sized f (Min n m) c
zipWith = S.zipWith @Nat

zipWithSame
  :: (Dom f a, Dom f b, Dom f c, CZip f, CFreeMonoid f)
  => (a -> b -> c) -> Sized f n a -> Sized f n b -> Sized f n c
zipWithSame = S.zipWithSame @Nat

unzip
  :: (Dom f a, Dom f b, Dom f (a, b), CUnzip f)
  => Sized f n (a, b) -> (Sized f n a, Sized f n b)
unzip = S.unzip @Nat

unzipWith
  :: (Dom f a, Dom f b, Dom f c, CUnzip f)
  => (a -> (b, c)) -> Sized f n a -> (Sized f n b, Sized f n c)
unzipWith = S.unzipWith @Nat

map
  :: (Dom f a, Dom f b, CFreeMonoid f)
  => (a -> b) -> Sized f n a -> Sized f n b
map = S.map @Nat

reverse :: (Dom f a, CFreeMonoid f) => Sized f n a -> Sized f n a
reverse = S.reverse @Nat

intersperse
  :: (Dom f a, CFreeMonoid f)
  => a -> Sized f n a -> Sized f ((2 * n) -. 1) a 
intersperse = S.intersperse @Nat

nub :: (Dom f a, Eq a, CFreeMonoid f) => Sized f n a -> SomeSized f a
nub = S.nub @Nat

sort :: (Dom f a, CFreeMonoid f, Ord a) => Sized f n a -> Sized f n a
sort = S.sort @Nat

sortBy
  :: (Dom f a, CFreeMonoid f)
  => (a -> a -> Ordering)
  -> Sized f n a -> Sized f n a
sortBy = S.sortBy @Nat

insert
  :: (Dom f a, CFreeMonoid f, Ord a)
  => a -> Sized f n a -> Sized f (n + 1) a
insert = S.insert @Nat

insertBy
  :: (Dom f a, CFreeMonoid f)
  => (a -> a -> Ordering) -> a -> Sized f n a -> Sized f (n + 1) a
insertBy = S.insertBy @Nat

toList :: (Dom f a, CFoldable f) => Sized f n a -> [a]
toList = S.toList @Nat

fromList :: (Dom f a, CFreeMonoid f) => SNat n -> [a] -> Maybe (Sized f n a)
fromList = S.fromList @Nat

fromList' :: (Dom f a, CFreeMonoid f, KnownNat n) => [a] -> Maybe (Sized f n a)
fromList' = S.fromList' @Nat

unsafeFromList :: (Dom f a, CFreeMonoid f) => SNat n -> [a] -> Sized f n a
unsafeFromList = S.unsafeFromList @Nat

unsafeFromList' :: (Dom f a, KnownNat n, CFreeMonoid f) => [a] -> Sized f n a
unsafeFromList' = S.unsafeFromList' @Nat

fromListWithDefault :: (Dom f a, CFreeMonoid f) => SNat n -> a -> [a] -> Sized f n a
fromListWithDefault = S.fromListWithDefault @Nat

fromListWithDefault' :: (Dom f a, KnownNat n, CFreeMonoid f)
  => a -> [a] -> Sized f n a
fromListWithDefault' = S.fromListWithDefault' @Nat

unsized :: Sized f n a -> f a
unsized = S.unsized @Nat

toSized :: (Dom f a, CFreeMonoid f) => SNat n -> f a -> Maybe (Sized f n a)
toSized = S.toSized @Nat

toSized' :: (Dom f a, CFreeMonoid f, KnownNat n) => f a -> Maybe (Sized f n a)
toSized' = S.toSized' @Nat

unsafeToSized :: SNat n -> f a -> Sized f n a
unsafeToSized = S.unsafeToSized @Nat

unsafeToSized' :: (Dom f a, KnownNat n) => f a -> Sized f n a
unsafeToSized' = S.unsafeToSized' @Nat

toSizedWithDefault :: (Dom f a, CFreeMonoid f) => SNat n -> a -> f a -> Sized f n a
toSizedWithDefault = S.toSizedWithDefault @Nat

toSizedWithDefault' :: (Dom f a, KnownNat n, CFreeMonoid f)
  => a -> f a -> Sized f n a
toSizedWithDefault' = S.toSizedWithDefault' @Nat

type Partitioned f (n :: Nat) a = S.Partitioned f n a

pattern Partitioned
  :: forall (f :: Type -> Type) (n :: Nat) a. ()
  => forall (n1 :: Nat) (m :: Nat). (n ~ (n1 + m), Dom f a)
  => SNat n1 -> Sized f n1 a -> SNat m
  -> Sized f m a -> Partitioned f n a
{-# COMPLETE Partitioned #-}
pattern Partitioned ls l rs r = S.Partitioned ls l rs r

takeWhile :: (Dom f a, CFreeMonoid f) => (a -> Bool) -> Sized f n a -> SomeSized f a
takeWhile = S.takeWhile @Nat

dropWhile :: (Dom f a, CFreeMonoid f) => (a -> Bool) -> Sized f n a -> SomeSized f a
dropWhile = S.dropWhile @Nat

span :: (Dom f a, CFreeMonoid f) => (a -> Bool) -> Sized f n a -> Partitioned f n a
span = S.span @Nat

break :: (Dom f a, CFreeMonoid f) => (a -> Bool) -> Sized f n a -> Partitioned f n a
break = S.break @Nat

partition :: (Dom f a, CFreeMonoid f) => (a -> Bool) -> Sized f n a -> Partitioned f n a
partition = S.partition @Nat

elem :: (Dom f a, CFoldable f, Eq a) => a -> Sized f n a -> Bool
elem = S.elem @Nat

notElem :: (Dom f a, CFoldable f, Eq a) => a -> Sized f n a -> Bool
notElem = S.notElem @Nat

find :: (Dom f a, CFoldable f) => (a -> Bool) -> Sized f n a -> Maybe a
find = S.find @Nat

findIndex :: (Dom f a, CFoldable f) => (a -> Bool) -> Sized f n a -> Maybe Int
findIndex = S.findIndex @Nat

sFindIndex :: (Dom f a, KnownNat n, CFoldable f) => (a -> Bool) -> Sized f n a -> Maybe (Ordinal n)
sFindIndex = S.sFindIndex @Nat

findIndices :: (Dom f a, CFoldable f) => (a -> Bool) -> Sized f n a -> [Int]
findIndices = S.findIndices @Nat

sFindIndices :: (Dom f a, CFoldable f, KnownNat n) => (a -> Bool) -> Sized f n a -> [Ordinal n]
sFindIndices = S.sFindIndices @Nat

elemIndex :: (Dom f a, CFoldable f) => (a -> Bool) -> Sized f n a -> Maybe Int
elemIndex = S.findIndex @Nat

sUnsafeElemIndex :: (Dom f a, KnownNat n, CFoldable f, Eq a) => a -> Sized f n a -> Maybe (Ordinal n)
{-# DEPRECATED sUnsafeElemIndex "Use sElemIndex instead" #-}
sUnsafeElemIndex = S.sElemIndex @Nat

sElemIndex :: (Dom f a, KnownNat n, CFoldable f) => (a -> Bool) -> Sized f n a -> Maybe (Ordinal n)
sElemIndex = S.sFindIndex @Nat

elemIndices :: (Dom f a, CFoldable f) => (a -> Bool) -> Sized f n a -> [Int]
elemIndices = S.findIndices @Nat

sElemIndices :: (Dom f a, CFoldable f, KnownNat n) => (a -> Bool) -> Sized f n a -> [Ordinal n]
sElemIndices = S.sFindIndices @Nat

type ConsView f (n :: Nat) a = S.ConsView f n a

viewCons :: (Dom f a, KnownNat n, CFreeMonoid f) => Sized f n a -> ConsView f n a
viewCons = S.viewCons @Nat

type SnocView f (n :: Nat) a = S.SnocView f n a

viewSnoc :: (Dom f a, KnownNat n, CFreeMonoid f) => Sized f n a -> ConsView f n a
viewSnoc = S.viewCons @Nat

pattern (:<)
  :: forall (f :: Type -> Type) a (n :: Nat).
      (Dom f a, SingI n, CFreeMonoid f)
  => forall (n1 :: Nat). (n ~ Succ n1, SingI n1)
  => a -> Sized f n1 a -> Sized f n a
pattern a :< b = a S.:< b
infixr 5 :<

pattern NilL :: forall f (n :: Nat) a.
                (KnownNat n, CFreeMonoid f, Dom f a)
             => n ~ 0 => Sized f n a
pattern NilL = S.NilL

pattern (:>)
  :: forall (f :: Type -> Type) a (n :: Nat). 
      (Dom f a, SingI n, CFreeMonoid f)
  => forall (n1 :: Nat). (n ~ (n1 + 1), SingI n1)
  => Sized f n1 a -> a -> Sized f n a
pattern a :> b = a S.:> b
infixl 5 :>

pattern NilR :: forall f (n :: Nat) a.
                (CFreeMonoid f, Dom f a,  SingI n)
             => n ~ 0 => Sized f n a
pattern NilR = S.NilR
