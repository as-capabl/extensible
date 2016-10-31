{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE ViewPatterns, ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE MultiParamTypeClasses, UndecidableInstances #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ScopedTypeVariables #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Extensible.Product.Ordered
-- Copyright   :  (c) Hidenori Azuma 2016
-- License     :  BSD3
--
-- Maintainer  :  Fumiaki Kinoshita <fumiexcel@gmail.com>
-- Stability   :  experimental
-- Portability :  non-portable
--
------------------------------------------------------------------------
module Data.Extensible.Product.Ordered (
  -- * Ordered variations of basic operations
  hfoldMap
  , htraverse
  , hsequence
  , Forall (..)) where

import Data.Extensible.Internal
-- import Data.Extensible.Internal.Rig
import Data.Extensible.Product hiding (hfoldMap, htraverse, hsequence, Forall, hgenerateFor)
import Unsafe.Coerce
#if !MIN_VERSION_base(4,8,0)
import Control.Applicative
#endif
import Data.Monoid
-- import Data.Typeable (Typeable)
-- import Data.Extensible.Class
import Data.Functor.Identity
import Data.Extensible.Wrapper
-- import Data.Profunctor.Unsafe
-- import Data.Profunctor.Rep
-- import Data.Profunctor.Sieve
-- import Control.Comonad
import Control.Monad.Writer
import qualified Data.Sequence as Seq
import Data.Sequence (ViewL((:<)), (|>))


data ListProd (h :: k -> *) (s :: [k]) where
  ListNil :: ListProd h '[]
  ListCons :: !(h x) -> ListProd h xs -> ListProd h (x ': xs)


fromListProd :: ListProd h k -> (h :* k)
fromListProd ListNil = Nil
fromListProd (ListCons x xs) = let (a, b) = interleave xs in Tree x (fromListProd a) (fromListProd b)
  where
    interleave :: ListProd h xs -> (ListProd h (Half xs), ListProd h (Half (Tail xs)))
    interleave ListNil = (ListNil, ListNil)
    interleave (ListCons a b0) = case b0 of
      ListCons b rest ->
        let (as, bs) = interleave rest in (ListCons a as, unsafeCoerce $ ListCons b bs)
      ListNil -> (ListCons a ListNil, ListNil)


toListProd :: (h :* k) -> ListProd h k
toListProd Nil = ListNil
toListProd (Tree h a b) = ListCons h (unInterleave (toListProd a) (toListProd b))
  where
    unInterleave ::
      forall h xs ys. Tail xs ~ ys =>
      ListProd h (Half xs) -> ListProd h (Half ys) -> ListProd h xs
    unInterleave (ListCons a as) bs =
      unsafeCoerce $ ListCons a (unInterleave bs (unsafeCoerce as) :: ListProd h ys)
    unInterleave ListNil _ = unsafeCoerce ListNil

traverseListProd :: Applicative f => (forall x. g x -> f (h x)) -> ListProd g xs -> f (ListProd h xs)
traverseListProd _ ListNil = pure ListNil
traverseListProd f (ListCons a as) = ListCons <$> (f a) <*> traverseListProd f as

-- | Map elements to a monoid and combine the results.
--
-- @'hfoldMap' f . 'hmap' g ≡ 'hfoldMap' (f . g)@
hfoldMap :: Monoid a => (forall x. h x -> a) -> h :* xs -> a
hfoldMap _ Nil = mempty
hfoldMap f (Tree h a b) = f h `mappend` hfoldMapHelper f (Seq.fromList [SomeProd a, SomeProd b])
{-# INLINE hfoldMap #-}

data SomeProd h where
  SomeProd :: h :* xs -> SomeProd h

-- だめなやつ。20個目くらいで間違える。ListProdで書こう。
hfoldMapHelper :: Monoid a => (forall x. h x -> a) ->
                   Seq.Seq (SomeProd h) -> a
hfoldMapHelper f (Seq.viewl -> SomeProd Nil :< _) =
    mempty -- hfoldMapHelper f rest -- OK because the rest is all Nil
hfoldMapHelper f (Seq.viewl -> SomeProd (Tree h1 a1 b1) :< rest) =
  f h1 `mappend`
    case Seq.viewl rest of
      SomeProd (Tree h2 a2 b2) :< rest' ->
        f h2 `mappend`
          hfoldMapHelper f (rest' |> SomeProd a1 |> SomeProd a2 |> SomeProd b1 |> SomeProd b2)
      SomeProd Nil :< rest' ->
        hfoldMapHelper f rest'
      Seq.EmptyL ->
        hfoldMapHelper f $ Seq.fromList [SomeProd a1, SomeProd b1]
hfoldMapHelper _ _ = mempty

-- | Traverse all elements and combine the result sequentially.
-- @
-- htraverse (fmap f . g) ≡ fmap (hmap f) . htraverse g
-- htraverse pure ≡ pure
-- htraverse (Comp . fmap g . f) ≡ Comp . fmap (htraverse g) . htraverse f
-- @
htraverse :: Applicative f => (forall x. g x -> f (h x)) -> g :* xs -> f (h :* xs)
htraverse f = (fromListProd <$>) . traverseListProd f . toListProd

{-# INLINE htraverse #-}


-- | 'sequence' analog for extensible products
hsequence :: Applicative f => Comp f h :* xs -> f (h :* xs)
hsequence = htraverse getComp
{-# INLINE hsequence #-}


-- | Guarantees the all elements satisfies the predicate.
class Forall c (xs :: [k]) where
  -- | /O(n)/ Analogous to 'hgenerate', but it also supplies a context @c x@ for every elements in @xs@.
  hgenerateFor :: Applicative f =>
                  proxy c -> (forall x. c x => Membership xs x -> f (h x)) -> f (h :* xs)

instance Forall c '[] where
  hgenerateFor _ _ = pure Nil
  {-# INLINE hgenerateFor #-}

instance (c x, Forall c (Half xs), Forall c (Half (Tail xs))) => Forall c (x ': xs) where
  hgenerateFor proxy f = Tree
    <$> f here
    <*> hgenerateFor proxy (f . navL)
    <*> hgenerateFor proxy (f . navR)
  {-# INLINE hgenerateFor #-}

