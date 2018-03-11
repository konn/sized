{-# LANGUAGE ConstraintKinds, DataKinds, DeriveDataTypeable, DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable, ExplicitNamespaces, FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances, GeneralizedNewtypeDeriving, KindSignatures #-}
{-# LANGUAGE LiberalTypeSynonyms, MultiParamTypeClasses, PolyKinds         #-}
{-# LANGUAGE RankNTypes, ScopedTypeVariables, StandaloneDeriving           #-}
{-# LANGUAGE TypeFamilies, TypeInType, TypeOperators, UndecidableInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Data.Sized.Internal
       (Sized(..),instLL, instFunctor, ListLikeF,
        withListLikeF, withListLikeF'
       ) where
import           Control.DeepSeq         (NFData (..))
import           Control.Lens.At         (Index, IxValue, Ixed (..))
import           Control.Lens.Indexed    (FoldableWithIndex (..),
                                          FunctorWithIndex (..),
                                          TraversableWithIndex (..))
import           Data.Constraint         ((:-) (..), (:=>) (..), Class (..),
                                          Dict (..), trans, weaken1, weaken2,
                                          (&&&), (\\))
import           Data.Constraint.Forall  (Forall, inst)
import           Data.Foldable           (Foldable)
import           Data.Hashable           (Hashable (..))
import           Data.Kind               (Type)
import           Data.ListLike           (ListLike)
import           Data.MonoTraversable    (Element, MonoFoldable (..),
                                          MonoFunctor (..),
                                          MonoTraversable (..))
import           Data.Proxy              (Proxy (..))
import qualified Data.Sequence           as Seq
import           Data.Singletons.Prelude (SingI)
import           Data.Traversable        (Traversable)
import qualified Data.Type.Natural       as PN
import           Data.Type.Ordinal       (HasOrdinal, Ordinal (..),
                                          ordToNatural, unsafeNaturalToOrd)
import           Data.Typeable           (Typeable)
import qualified Data.Vector             as V
import qualified Data.Vector.Storable    as SV
import qualified Data.Vector.Unboxed     as UV
import qualified GHC.TypeLits            as TL

-- | @Sized@ wraps a sequential type 'f' and makes length-parametrized version.
--
-- Here, 'f' must be the instance of 'Functor' and @'ListLike' (f a) a@ for all @a@.
-- This constraint is expressed by 'ListLikeF'.
-- Folding and traversing function such as 'all' and 'foldl'' is available
-- via 'Foldable' or 'Traversable' class, if 'f' is the instance of them.
--
-- Since 0.2.0.0
newtype Sized (f :: Type -> Type) (n :: nat) a =
  Sized { runSized :: f a
        } deriving (Eq, Ord, Typeable,
                    Functor, Foldable, Traversable)

type instance Element (Sized f n a) = Element (f a)

-- | Since 0.2.0.0
deriving instance MonoFoldable (f a)
               => MonoFoldable (Sized f n a)

-- | Since 0.2.0.0
deriving instance MonoFunctor (f a)
               => MonoFunctor (Sized f n a)

-- | Since 0.2.0.0
instance {-# OVERLAPPABLE #-} (MonoTraversable (f a))
      => MonoTraversable (Sized f n a) where
  {-# SPECIALISE instance MonoTraversable (Sized [] n a) #-}
  {-# SPECIALISE instance MonoTraversable (Sized V.Vector n a) #-}
  {-# SPECIALISE instance MonoTraversable (Sized Seq.Seq n a) #-}
  {-# SPECIALISE instance UV.Unbox a => MonoTraversable (Sized UV.Vector n a) #-}
  {-# SPECIALISE instance SV.Storable a => MonoTraversable (Sized SV.Vector n a) #-}
  otraverse f = fmap Sized . otraverse f . runSized
  omapM f = fmap Sized . omapM f. runSized

-- | Since 0.2.0.0
instance {-# OVERLAPS #-} SV.Storable a => MonoTraversable (Sized SV.Vector n a) where
  otraverse f = fmap Sized . otraverse f . runSized
  omapM f = fmap Sized . omapM f . runSized

-- | Since 0.2.0.0
instance {-# OVERLAPS #-} UV.Unbox a => MonoTraversable (Sized UV.Vector n a) where
  otraverse f = fmap Sized . otraverse f . runSized
  omapM f = fmap Sized . omapM f . runSized

deriving instance NFData (f a) => NFData (Sized f n a)
deriving instance Hashable (f a) => Hashable (Sized f n a)

instance Show (f a) => Show (Sized f n a) where
  showsPrec d (Sized x) = showsPrec d x

-- | Since 0.2.0.0
type instance Index (Sized f n a) = Ordinal n

-- | Since 0.3.0.0
type instance IxValue (Sized f n a) = IxValue (f a)
instance (Integral (Index (f a)), Ixed (f a), HasOrdinal nat)
         => Ixed (Sized f (n :: nat) a) where
  {-# SPECIALISE instance Ixed (Sized [] (n :: TL.Nat) a) #-}
  {-# SPECIALISE instance Ixed (Sized [] (n :: PN.Nat) a) #-}
  {-# SPECIALISE instance Ixed (Sized V.Vector (n :: TL.Nat) a) #-}
  {-# SPECIALISE instance Ixed (Sized V.Vector (n :: PN.Nat) a) #-}
  {-# SPECIALISE instance SV.Storable a => Ixed (Sized SV.Vector (n :: TL.Nat) a) #-}
  {-# SPECIALISE instance SV.Storable a => Ixed (Sized SV.Vector (n :: PN.Nat) a) #-}
  {-# SPECIALISE instance UV.Unbox a => Ixed (Sized UV.Vector (n :: TL.Nat) a) #-}
  {-# SPECIALISE instance UV.Unbox a => Ixed (Sized UV.Vector (n :: PN.Nat) a) #-}
  {-# SPECIALISE instance Ixed (Sized Seq.Seq (n :: TL.Nat) a) #-}
  {-# SPECIALISE instance Ixed (Sized Seq.Seq (n :: PN.Nat) a) #-}
  {-# INLINE ix #-}
  ix n f = fmap Sized . ix (fromIntegral $ ordToNatural n) f . runSized

-- | Since 0.2.0.0
instance (Integral i, FunctorWithIndex i f, HasOrdinal nat, SingI n)
      => FunctorWithIndex (Ordinal (n :: nat)) (Sized f n) where
  imap f = Sized . imap (f . unsafeNaturalToOrd . fromIntegral) . runSized
  {-# INLINE imap #-}
  {-# SPECIALISE instance TL.KnownNat n
                       => FunctorWithIndex (Ordinal n) (Sized [] (n :: TL.Nat)) #-}
  {-# SPECIALISE instance SingI n
                       => FunctorWithIndex (Ordinal n) (Sized [] (n :: PN.Nat)) #-}
  {-# SPECIALISE instance TL.KnownNat n
                       => FunctorWithIndex (Ordinal n) (Sized V.Vector (n :: TL.Nat)) #-}
  {-# SPECIALISE instance SingI n
                       => FunctorWithIndex (Ordinal n) (Sized V.Vector (n :: PN.Nat)) #-}
  {-# SPECIALISE instance TL.KnownNat n
                       => FunctorWithIndex (Ordinal n) (Sized Seq.Seq (n :: TL.Nat)) #-}
  {-# SPECIALISE instance SingI n
                       => FunctorWithIndex (Ordinal n) (Sized Seq.Seq (n :: PN.Nat)) #-}

-- | Since 0.2.0.0
instance (Integral i, FoldableWithIndex i f, HasOrdinal nat, SingI n)
      => FoldableWithIndex (Ordinal (n :: nat)) (Sized f n) where
  ifoldMap f = ifoldMap (f . unsafeNaturalToOrd . fromIntegral) . runSized
  {-# INLINE ifoldMap #-}

  ifoldr f e = ifoldr (f . unsafeNaturalToOrd . fromIntegral) e . runSized
  {-# INLINE ifoldr #-}

  ifoldl f e = ifoldl (f . unsafeNaturalToOrd . fromIntegral) e . runSized
  {-# INLINE ifoldl #-}

  ifoldr' f e = ifoldr' (f . unsafeNaturalToOrd . fromIntegral) e . runSized
  {-# INLINE ifoldr' #-}

  ifoldl' f e = ifoldl' (f . unsafeNaturalToOrd . fromIntegral) e . runSized
  {-# INLINE ifoldl' #-}

  {-# SPECIALISE instance TL.KnownNat n
                       => FoldableWithIndex (Ordinal n) (Sized [] (n :: TL.Nat)) #-}
  {-# SPECIALISE instance SingI n
                       => FoldableWithIndex (Ordinal n) (Sized [] (n :: PN.Nat)) #-}
  {-# SPECIALISE instance TL.KnownNat n
                       => FoldableWithIndex (Ordinal n) (Sized V.Vector (n :: TL.Nat)) #-}
  {-# SPECIALISE instance SingI n
                       => FoldableWithIndex (Ordinal n) (Sized V.Vector (n :: PN.Nat)) #-}
  {-# SPECIALISE instance TL.KnownNat n
                       => FoldableWithIndex (Ordinal n) (Sized Seq.Seq (n :: TL.Nat)) #-}
  {-# SPECIALISE instance SingI n
                       => FoldableWithIndex (Ordinal n) (Sized Seq.Seq (n :: PN.Nat)) #-}

-- | Since 0.2.0.0
instance (Integral i, TraversableWithIndex i f, HasOrdinal nat, SingI n)
      => TraversableWithIndex (Ordinal (n :: nat)) (Sized f n) where
  itraverse f = fmap Sized . itraverse (f . unsafeNaturalToOrd . fromIntegral) . runSized
  {-# INLINE itraverse #-}

  {-# SPECIALISE instance TL.KnownNat n
                       => TraversableWithIndex (Ordinal n) (Sized [] (n :: TL.Nat)) #-}
  {-# SPECIALISE instance SingI n
                       => TraversableWithIndex (Ordinal n) (Sized [] (n :: PN.Nat)) #-}
  {-# SPECIALISE instance TL.KnownNat n
                       => TraversableWithIndex (Ordinal n) (Sized V.Vector (n :: TL.Nat)) #-}
  {-# SPECIALISE instance SingI n
                       => TraversableWithIndex (Ordinal n) (Sized V.Vector (n :: PN.Nat)) #-}
  {-# SPECIALISE instance TL.KnownNat n
                       => TraversableWithIndex (Ordinal n) (Sized Seq.Seq (n :: TL.Nat)) #-}
  {-# SPECIALISE instance SingI n
                       => TraversableWithIndex (Ordinal n) (Sized Seq.Seq (n :: PN.Nat))  #-}

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
{-# INLINE [1] instLLF #-}
{-# RULES
"instLLF/List" [~1]
  instLLF = Sub Dict :: Forall (LLF []) :- ListLike [a] a
"instLLF/Seq" [~1]
  instLLF = Sub Dict :: Forall (LLF Seq.Seq) :- ListLike (Seq.Seq a) a
"instLLF/Vector" [~1]
  instLLF = Sub Dict :: Forall (LLF V.Vector) :- ListLike (V.Vector a) a
  #-}

instLL :: forall f a. ListLikeF f :- ListLike (f a) a
instLL = trans instLLF weaken2
{-# INLINE [1] instLL #-}
{-# RULES
"instLL/List" [~1]
  instLL = Sub Dict :: ListLikeF [] :- ListLike [a] a
"instLL/Seq" [~1]
  instLL = Sub Dict :: ListLikeF Seq.Seq :- ListLike (Seq.Seq a) a
"instLL/Vector" [~1]
  instLL = Sub Dict :: ListLikeF V.Vector :- ListLike (V.Vector a) a
  #-}


instFunctor :: ListLikeF f :- Functor f
instFunctor = weaken1
{-# INLINE [1] instFunctor #-}
{-# RULES
"instFunctor/List" [~1]
  instFunctor = Sub Dict :: ListLikeF [] :- Functor []
"instFunctor/Seq" [~1]
  instFunctor = Sub Dict :: ListLikeF Seq.Seq :- Functor Seq.Seq
"instFunctor/Vector" [~1]
  instFunctor = Sub Dict :: ListLikeF V.Vector :- Functor V.Vector
  #-}

withListLikeF :: forall pxy f a b. ListLikeF f
              => pxy (f a) -> ((Functor f, ListLike (f a) a) => b) -> b
withListLikeF _ b = b \\ llDic &&& instFunctor
  where
    llDic = instLL :: ListLikeF f :- ListLike (f a) a
{-# RULES
"withListLikeF/List" [~1] forall (pxy :: proxy [a]).
  withListLikeF pxy = id
"withListLikeF/Seq" [~1] forall (pxy :: proxy (Seq.Seq a)).
  withListLikeF pxy = id
"withListLikeF/Vector" [~1] forall (pxy :: proxy (V.Vector a)).
  withListLikeF pxy = id
 #-}
{-# INLINE [1] withListLikeF #-}

withListLikeF' :: ListLikeF f => f a -> ((Functor f, ListLike (f a) a) => b) -> b
withListLikeF' xs = withListLikeF (toProxy xs)
{-# RULES
"withListLikeF'/List" [~1] forall (pxy :: [a]).
  withListLikeF' pxy = id
"withListLikeF'/Seq" [~1] forall (pxy :: (Seq.Seq a)).
  withListLikeF' pxy = id
"withListLikeF'/Vector" [~1] forall (pxy ::(V.Vector a)).
  withListLikeF' pxy = id
 #-}
{-# INLINE [1] withListLikeF' #-}

toProxy :: a -> Proxy a
toProxy _ = Proxy
