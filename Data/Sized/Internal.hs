{-# LANGUAGE ConstraintKinds, DataKinds, DeriveDataTypeable, DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable, EmptyDataDecls, FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances, GeneralizedNewtypeDeriving, KindSignatures #-}
{-# LANGUAGE LiberalTypeSynonyms, MultiParamTypeClasses, PolyKinds         #-}
{-# LANGUAGE RankNTypes, ScopedTypeVariables, TypeFamilies, TypeOperators  #-}
{-# LANGUAGE UndecidableInstances                                          #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Data.Sized.Internal
       (Sized(..), instLL, instFunctor, ListLikeF,
        withListLikeF, withListLikeF', givenListLikeF,
        givenListLikeF') where
import           Data.Constraint
import           Data.Constraint.Forall (Forall, inst)
import           Data.Foldable          (Foldable)
import           Data.ListLike          (FoldableLL (..), ListLike)
import qualified Data.ListLike          as LL
import           Data.Proxy
import qualified Data.Sequence          as Seq
import           Data.Traversable       (Traversable)
import           Data.Type.Natural      (Nat)
import           Data.Typeable          (Typeable)
import qualified Data.Vector            as V

-- | @Sized@ wraps a sequential type 'f' and makes length-parametrized version.
--   GHC's type natural is currently poor, so we adopt Peano numeral here.
--
-- Here, 'f' must be the instance of 'Functor' and @'ListLike' (f a) a@ for all @a@.
-- This constraint is expressed by 'ListLikeF'.
-- Folding and traversing function such as 'all' and 'foldl'' is available
-- via 'Foldable' or 'Traversable' class, if 'f' is the instance of them.
--
-- Since 0.1.0.0
newtype Sized f (n :: Nat) a =
  Sized { runSized :: f a
        } deriving (Eq, Ord, Typeable,
                    Functor, Foldable, Traversable)

-- | Since 0.1.0.0
instance ListLikeF f => FoldableLL (Sized f n a) a where
  {-# SPECIALISE instance LL.FoldableLL (Sized [] n a) a #-}
  {-# SPECIALISE instance LL.FoldableLL (Sized V.Vector n a) a #-}
  {-# SPECIALISE instance LL.FoldableLL (Sized Seq.Seq n a) a #-}
  foldl  f a = givenListLikeF' $ LL.foldl f a
  {-# INLINE foldl #-}
  foldl' f a = givenListLikeF' $ LL.foldl' f a
  {-# INLINE foldl' #-}
  foldl1 f   = givenListLikeF' $ LL.foldl1 f
  {-# INLINE foldl1 #-}
  foldr  f a = givenListLikeF' $ LL.foldr f a
  {-# INLINE foldr #-}
  foldr' f a = givenListLikeF' $ LL.foldr' f a
  {-# INLINE foldr' #-}
  foldr1 f   = givenListLikeF' $ LL.foldr1 f
  {-# INLINE foldr1 #-}

instance Show (f a) => Show (Sized f n a) where
  showsPrec d (Sized x) = showsPrec d x
class (ListLike (f a) a) => LLF f a
instance (ListLike (f a) a) => LLF f a

instance Class (ListLike (f a) a) (LLF f a) where
  cls = Sub Dict
instance (LLF f a) :=> (ListLike (f a) a) where
  ins = Sub Dict

-- | Functor @f@ such that there is instance @ListLike (f a) a@ for any @a@.
--
-- Since 0.1.0.0
type ListLikeF f = (Functor f, Forall (LLF f))

instLLF :: forall f a. Forall (LLF f) :- ListLike (f a) a
instLLF = trans ins inst
{-# INLINE instLLF #-}

instLL :: forall f a. ListLikeF f :- ListLike (f a) a
instLL = trans instLLF weaken2
{-# INLINE instLL #-}

instFunctor :: ListLikeF f :- Functor f
instFunctor = weaken1
{-# INLINE instFunctor #-}

givenListLikeF :: ListLikeF f => ((Functor f, ListLike (f a) a) => f a ->  b) -> f a -> b
givenListLikeF = withListLikeF Proxy
{-# INLINE givenListLikeF #-}

givenListLikeF' :: ListLikeF f => ((Functor f, ListLike (f a) a) => f a ->  b) -> Sized f n a -> b
givenListLikeF' f = givenListLikeF f . runSized
{-# INLINE givenListLikeF' #-}

withListLikeF :: forall pxy f a b. ListLikeF f
              => pxy (f a) -> ((Functor f, ListLike (f a) a) => b) -> b
withListLikeF _ b = b \\ llDic &&& instFunctor
  where
    llDic = instLL :: ListLikeF f :- ListLike (f a) a
{-# INLINE withListLikeF #-}

withListLikeF' :: ListLikeF f => f a -> ((Functor f, ListLike (f a) a) => b) -> b
withListLikeF' xs = withListLikeF (toProxy xs)
{-# INLINE withListLikeF' #-}

toProxy :: a -> Proxy a
toProxy = const Proxy
{-# INLINE toProxy #-}

instance Class (FoldableLL f a) (ListLike f a) where
  cls = Sub Dict

instance ListLike f a :=> FoldableLL f a where
  ins = Sub Dict

