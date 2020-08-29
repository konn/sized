{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE TypeOperators, NoImplicitPrelude #-}
{-# LANGUAGE CPP, DataKinds, GADTs, KindSignatures, MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms, PolyKinds, RankNTypes, TypeInType           #-}
{-# LANGUAGE ViewPatterns                                                 #-}
{-# LANGUAGE NoStarIsType #-}
-- | This module exports @'S.Sized'@ type and
--   functions specialized to
--   GHC's built-in type numeral @'TL.Nat'@.
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
import qualified GHC.TypeLits                 as TL
import GHC.TypeNats (type (+), KnownNat) 
import Prelude (Maybe, Ordering, Ord, Eq, Monoid, Bool(..), Int)
import Data.Singletons.TypeLits (SNat)
import Data.Singletons.Prelude (POrd((<=)))
import Data.Type.Natural.Class (type (-.), type (<))
import Data.Type.Natural (Min)
import GHC.TypeLits (type (-))

type Ordinal = (O.Ordinal :: TL.Nat -> Type)
type Sized = (S.Sized :: (Type -> Type) -> TL.Nat -> Type -> Type)

type SomeSized f a = S.SomeSized' f TL.Nat a

pattern SomeSized
  :: forall (f :: Type -> Type) a. ()
  => forall (n :: TL.Nat). SNat n
  -> Sized f n a -> SomeSized f a
{-# COMPLETE SomeSized #-}
pattern SomeSized n s = S.SomeSized'  n s

length :: (Dom f a, CFoldable f, KnownNat n) => Sized f n a -> Int
length = S.length @TL.Nat

sLength :: (Dom f a, CFoldable f) => Sized f n a -> SNat n
sLength = S.sLength @TL.Nat

null :: (Dom f a, CFoldable f) => Sized f n a -> Bool
null = S.null @TL.Nat

(!!) :: (Dom f a, CFoldable f, (1 <= m) ~ 'True) => Sized f m a -> Int -> a
(!!) = (S.!!) @TL.Nat

(%!!) :: (Dom f c, CFoldable f) => Sized f n c -> Ordinal n -> c
(%!!) = (S.%!!) @TL.Nat

index
  :: (Dom f a, CFoldable f, (1 <= m) ~ 'True)
  => Int -> Sized f m a -> a
index = S.index @TL.Nat

sIndex :: (Dom f c, CFoldable f) => Ordinal n -> Sized f n c -> c
sIndex = S.sIndex @TL.Nat

head :: (Dom f a, CFoldable f, (0 < n) ~ 'True) => Sized f n a -> a
head = S.head @TL.Nat

last :: (Dom f a, CFoldable f, (0 < n) ~ 'True) => Sized f n a -> a
last = S.last @TL.Nat

uncons
  :: (Dom f a, KnownNat n, CFreeMonoid f, (0 < n) ~ 'True)
  => Sized f n a -> Uncons f n a
uncons = S.uncons @TL.Nat

uncons'
  :: (Dom f a, KnownNat n, CFreeMonoid f, (0 < n) ~ 'True)
  => Sized f n a
  -> Uncons f n a
uncons' = S.uncons @TL.Nat

unsnoc
  :: (Dom f a, KnownNat n, CFreeMonoid f, (0 < n) ~ 'True)
  => Sized f n a -> Unsnoc f n a
unsnoc = S.unsnoc @TL.Nat

unsnoc' :: (Dom f a, KnownNat n, CFreeMonoid f) => proxy n -> Sized f (n + 1) a -> Unsnoc f (n + 1) a
unsnoc' = S.unsnoc' @TL.Nat

type Uncons f (n :: TL.Nat) a = S.Uncons f n a
pattern Uncons
  :: forall (f :: Type -> Type) (n :: TL.Nat) a. ()
  => forall (n1 :: TL.Nat). (n ~ Succ n1, SingI n1)
  => a -> Sized f n1 a -> Uncons f n a
pattern Uncons a as = S.Uncons a as

type Unsnoc f (n :: TL.Nat) a = S.Unsnoc f n a

pattern Unsnoc
  :: forall (f :: Type -> Type) (n :: TL.Nat) a. ()
  => forall (n1 :: TL.Nat). (n ~ Succ n1)
  => Sized f n1 a -> a -> Unsnoc f n a
pattern Unsnoc xs x = S.Unsnoc xs x

tail :: (Dom f a, CFreeMonoid f) => Sized f (1 + n) a -> Sized f n a
tail = S.tail @TL.Nat

init :: (Dom f a, CFreeMonoid f) => Sized f (n + 1) a -> Sized f n a
init = S.init @TL.Nat

take
  :: (Dom f a, CFreeMonoid f, (n <= m) ~ 'True)
  => SNat n -> Sized f m a -> Sized f n a
take = S.take @TL.Nat

takeAtMost
  :: (Dom f a, CFreeMonoid f)
  => SNat n -> Sized f m a -> Sized f (Min n m) a
takeAtMost = S.takeAtMost @TL.Nat

drop
  :: (Dom f a, CFreeMonoid f, (n <= m) ~ 'True)
  => SNat n -> Sized f m a -> Sized f (m TL.- n) a
drop = S.drop @TL.Nat

splitAt
  :: (Dom f a, CFreeMonoid f, (n <= m) ~ 'True)
  => SNat n -> Sized f m a -> (Sized f n a, Sized f (m - n) a)
splitAt = S.splitAt @TL.Nat

splitAtMost
  :: (Dom f a, CFreeMonoid f)
  => SNat n -> Sized f m a
  -> (Sized f (Min n m) a, Sized f (m -. n) a)
splitAtMost = S.splitAtMost @TL.Nat

empty :: (Dom f a, Monoid (f a)) => Sized f 0 a
empty = S.empty @TL.Nat

singleton :: (Dom f a, CFreeMonoid f) => a -> Sized f 1 a
singleton = S.singleton @TL.Nat

toSomeSized :: (Dom f a, CFoldable f) => f a -> SomeSized f a
toSomeSized = S.toSomeSized @TL.Nat

replicate :: (Dom f a, CFreeMonoid f) => SNat n -> a -> Sized f n a
replicate = S.replicate @TL.Nat

replicate' :: (Dom f a, CFreeMonoid f) => SNat n -> a -> Sized f n a
replicate' = S.replicate @TL.Nat

generate :: (Dom f a, CFreeMonoid f, KnownNat n) => SNat n -> (Ordinal n -> a) -> Sized f n a
generate = S.generate @TL.Nat

cons :: (Dom f a, CFreeMonoid f) => a -> Sized f n a -> Sized f (n + 1) a
cons = S.cons @TL.Nat

snoc :: (Dom f a, CFreeMonoid f) => Sized f n a -> a -> Sized f (n + 1) a
snoc = S.snoc @TL.Nat

(<|) :: (Dom f a, CFreeMonoid f) => a -> Sized f n a -> Sized f (n + 1) a
(<|) = (S.<|) @TL.Nat

(|>) :: (Dom f a, CFreeMonoid f) => Sized f n a -> a -> Sized f (n + 1) a
(|>) = (S.|>) @TL.Nat

(++) :: (Dom f a, CFreeMonoid f) => Sized f n a -> Sized f m a -> Sized f (n + m) a
(++) = (S.++) @TL.Nat

append :: (Dom f a, CFreeMonoid f) => Sized f n a -> Sized f m a -> Sized f (n + m) a
append = S.append @TL.Nat

concat
  :: (Dom f a, Dom f' (f a), Dom f' (Sized f n a),
      CFreeMonoid f, CFunctor f', CFoldable f'
    ) => Sized f' m (Sized f n a) -> Sized f (m TL.* n) a
concat = S.concat @TL.Nat

zip :: (Dom f a, Dom f b, Dom f (a, b), CZip f)
  => Sized f n a -> Sized f m b -> Sized f (Min n m) (a, b)
zip = S.zip @TL.Nat

zipSame :: (Dom f a, Dom f b, Dom f (a, b), CZip f)
  => Sized f n a -> Sized f n b -> Sized f n (a, b)
zipSame = S.zipSame @TL.Nat

zipWith :: (Dom f a, Dom f b, Dom f c, CZip f, CFreeMonoid f)
  => (a -> b -> c) -> Sized f n a -> Sized f m b -> Sized f (Min n m) c
zipWith = S.zipWith @TL.Nat

zipWithSame
  :: (Dom f a, Dom f b, Dom f c, CZip f, CFreeMonoid f)
  => (a -> b -> c) -> Sized f n a -> Sized f n b -> Sized f n c
zipWithSame = S.zipWithSame @TL.Nat

unzip
  :: (Dom f a, Dom f b, Dom f (a, b), CUnzip f)
  => Sized f n (a, b) -> (Sized f n a, Sized f n b)
unzip = S.unzip @TL.Nat

unzipWith
  :: (Dom f a, Dom f b, Dom f c, CUnzip f)
  => (a -> (b, c)) -> Sized f n a -> (Sized f n b, Sized f n c)
unzipWith = S.unzipWith @TL.Nat

map
  :: (Dom f a, Dom f b, CFreeMonoid f)
  => (a -> b) -> Sized f n a -> Sized f n b
map = S.map @TL.Nat

reverse :: (Dom f a, CFreeMonoid f) => Sized f n a -> Sized f n a
reverse = S.reverse @TL.Nat

intersperse
  :: (Dom f a, CFreeMonoid f)
  => a -> Sized f n a -> Sized f ((2 TL.* n) -. 1) a 
intersperse = S.intersperse @TL.Nat

nub :: (Dom f a, Eq a, CFreeMonoid f) => Sized f n a -> SomeSized f a
nub = S.nub @TL.Nat

sort :: (Dom f a, CFreeMonoid f, Ord a) => Sized f n a -> Sized f n a
sort = S.sort @TL.Nat

sortBy
  :: (Dom f a, CFreeMonoid f)
  => (a -> a -> Ordering)
  -> Sized f n a -> Sized f n a
sortBy = S.sortBy @TL.Nat

insert
  :: (Dom f a, CFreeMonoid f, Ord a)
  => a -> Sized f n a -> Sized f (n + 1) a
insert = S.insert @TL.Nat

insertBy
  :: (Dom f a, CFreeMonoid f)
  => (a -> a -> Ordering) -> a -> Sized f n a -> Sized f (n + 1) a
insertBy = S.insertBy @TL.Nat

toList :: (Dom f a, CFoldable f) => Sized f n a -> [a]
toList = S.toList @TL.Nat

fromList :: (Dom f a, CFreeMonoid f) => SNat n -> [a] -> Maybe (Sized f n a)
fromList = S.fromList @TL.Nat

fromList' :: (Dom f a, CFreeMonoid f, KnownNat n) => [a] -> Maybe (Sized f n a)
fromList' = S.fromList' @TL.Nat

unsafeFromList :: (Dom f a, CFreeMonoid f) => SNat n -> [a] -> Sized f n a
unsafeFromList = S.unsafeFromList @TL.Nat

unsafeFromList' :: (Dom f a, KnownNat n, CFreeMonoid f) => [a] -> Sized f n a
unsafeFromList' = S.unsafeFromList' @TL.Nat

fromListWithDefault :: (Dom f a, CFreeMonoid f) => SNat n -> a -> [a] -> Sized f n a
fromListWithDefault = S.fromListWithDefault @TL.Nat

fromListWithDefault' :: (Dom f a, KnownNat n, CFreeMonoid f)
  => a -> [a] -> Sized f n a
fromListWithDefault' = S.fromListWithDefault' @TL.Nat

unsized :: Sized f n a -> f a
unsized = S.unsized @TL.Nat

toSized :: (Dom f a, CFreeMonoid f) => SNat n -> f a -> Maybe (Sized f n a)
toSized = S.toSized @TL.Nat

toSized' :: (Dom f a, CFreeMonoid f, KnownNat n) => f a -> Maybe (Sized f n a)
toSized' = S.toSized' @TL.Nat

unsafeToSized :: SNat n -> f a -> Sized f n a
unsafeToSized = S.unsafeToSized @TL.Nat

unsafeToSized' :: (Dom f a, KnownNat n) => f a -> Sized f n a
unsafeToSized' = S.unsafeToSized' @TL.Nat

toSizedWithDefault :: (Dom f a, CFreeMonoid f) => SNat n -> a -> f a -> Sized f n a
toSizedWithDefault = S.toSizedWithDefault @TL.Nat

toSizedWithDefault' :: (Dom f a, KnownNat n, CFreeMonoid f)
  => a -> f a -> Sized f n a
toSizedWithDefault' = S.toSizedWithDefault' @TL.Nat

type Partitioned f (n :: TL.Nat) a = S.Partitioned f n a

pattern Partitioned
  :: forall (f :: Type -> Type) (n :: TL.Nat) a. ()
  => forall (n1 :: TL.Nat) (m :: TL.Nat). (n ~ (n1 + m), Dom f a)
  => SNat n1 -> Sized f n1 a -> SNat m
  -> Sized f m a -> Partitioned f n a
{-# COMPLETE Partitioned #-}
pattern Partitioned ls l rs r = S.Partitioned ls l rs r

takeWhile :: (Dom f a, CFreeMonoid f) => (a -> Bool) -> Sized f n a -> SomeSized f a
takeWhile = S.takeWhile @TL.Nat

dropWhile :: (Dom f a, CFreeMonoid f) => (a -> Bool) -> Sized f n a -> SomeSized f a
dropWhile = S.dropWhile @TL.Nat

span :: (Dom f a, CFreeMonoid f) => (a -> Bool) -> Sized f n a -> Partitioned f n a
span = S.span @TL.Nat

break :: (Dom f a, CFreeMonoid f) => (a -> Bool) -> Sized f n a -> Partitioned f n a
break = S.break @TL.Nat

partition :: (Dom f a, CFreeMonoid f) => (a -> Bool) -> Sized f n a -> Partitioned f n a
partition = S.partition @TL.Nat

elem :: (Dom f a, CFoldable f, Eq a) => a -> Sized f n a -> Bool
elem = S.elem @TL.Nat

notElem :: (Dom f a, CFoldable f, Eq a) => a -> Sized f n a -> Bool
notElem = S.notElem @TL.Nat

find :: (Dom f a, CFoldable f) => (a -> Bool) -> Sized f n a -> Maybe a
find = S.find @TL.Nat

findIndex :: (Dom f a, CFoldable f) => (a -> Bool) -> Sized f n a -> Maybe Int
findIndex = S.findIndex @TL.Nat

sFindIndex :: (Dom f a, KnownNat n, CFoldable f) => (a -> Bool) -> Sized f n a -> Maybe (Ordinal n)
sFindIndex = S.sFindIndex @TL.Nat

findIndices :: (Dom f a, CFoldable f) => (a -> Bool) -> Sized f n a -> [Int]
findIndices = S.findIndices @TL.Nat

sFindIndices :: (Dom f a, CFoldable f, KnownNat n) => (a -> Bool) -> Sized f n a -> [Ordinal n]
sFindIndices = S.sFindIndices @TL.Nat

elemIndex :: (Dom f a, CFoldable f) => (a -> Bool) -> Sized f n a -> Maybe Int
elemIndex = S.findIndex @TL.Nat

sUnsafeElemIndex :: (Dom f a, KnownNat n, CFoldable f, Eq a) => a -> Sized f n a -> Maybe (Ordinal n)
{-# DEPRECATED sUnsafeElemIndex "Use sElemIndex instead" #-}
sUnsafeElemIndex = S.sElemIndex @TL.Nat

sElemIndex :: (Dom f a, KnownNat n, CFoldable f) => (a -> Bool) -> Sized f n a -> Maybe (Ordinal n)
sElemIndex = S.sFindIndex @TL.Nat

elemIndices :: (Dom f a, CFoldable f) => (a -> Bool) -> Sized f n a -> [Int]
elemIndices = S.findIndices @TL.Nat

sElemIndices :: (Dom f a, CFoldable f, KnownNat n) => (a -> Bool) -> Sized f n a -> [Ordinal n]
sElemIndices = S.sFindIndices @TL.Nat

type ConsView f (n :: TL.Nat) a = S.ConsView f n a

viewCons :: (Dom f a, KnownNat n, CFreeMonoid f) => Sized f n a -> ConsView f n a
viewCons = S.viewCons @TL.Nat

type SnocView f (n :: TL.Nat) a = S.SnocView f n a

viewSnoc :: (Dom f a, KnownNat n, CFreeMonoid f) => Sized f n a -> ConsView f n a
viewSnoc = S.viewCons @TL.Nat

pattern (:<)
  :: forall (f :: Type -> Type) a (n :: TL.Nat).
      (Dom f a, SingI n, CFreeMonoid f)
  => forall (n1 :: TL.Nat). (n ~ Succ n1, SingI n1)
  => a -> Sized f n1 a -> Sized f n a
pattern a :< b = a S.:< b
infixr 5 :<

pattern NilL :: forall f (n :: TL.Nat) a.
                (TL.KnownNat n, CFreeMonoid f, Dom f a)
             => n ~ 0 => Sized f n a
pattern NilL = S.NilL

pattern (:>)
  :: forall (f :: Type -> Type) a (n :: TL.Nat). 
      (Dom f a, SingI n, CFreeMonoid f)
  => forall (n1 :: TL.Nat). (n ~ (n1 TL.+ 1), SingI n1)
  => Sized f n1 a -> a -> Sized f n a
pattern a :> b = a S.:> b
infixl 5 :>

pattern NilR :: forall f (n :: TL.Nat) a.
                (CFreeMonoid f, Dom f a,  SingI n)
             => n ~ 0 => Sized f n a
pattern NilR = S.NilR
