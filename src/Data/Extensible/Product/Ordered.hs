{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE ViewPatterns, ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE MultiParamTypeClasses, UndecidableInstances #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ScopedTypeVariables #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Extensible.Product.Ordered
-- Copyright   :  (c) Fumiaki Kinoshita, 2015
--                    Hidenori Azuma, 2016
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
  , hgenerate
  , hgenerateFor) where

import Data.Extensible.Internal
-- import Data.Extensible.Internal.Rig
import Data.Extensible.Product ((:*)(..))
import qualified Data.Extensible.Product as Xu
import Unsafe.Coerce
#if !MIN_VERSION_base(4,8,0)
import Control.Applicative
#endif
-- import Data.Monoid
import Data.Typeable (Typeable)
-- import Data.Extensible.Class
-- import Data.Functor.Identity
import Data.Extensible.Wrapper
import Data.Profunctor.Unsafe
-- import Data.Profunctor.Rep
-- import Data.Profunctor.Sieve
-- import Control.Comonad
-- import Control.Monad.Writer
-- import qualified Data.Sequence as Seq
-- import Data.Sequence (ViewL((:<)), (|>))


data ListProd (h :: k -> *) (s :: [k]) where
  ListNil :: ListProd h '[]
  ListCons :: !(h x) -> ListProd h xs -> ListProd h (x ': xs)

deriving instance Typeable ListProd

fromListProd :: ListProd h k -> h :* k
fromListProd ListNil = Nil
fromListProd (ListCons x xs) = let (a, b) = interleave xs in Tree x (fromListProd a) (fromListProd b)
  where
    interleave :: ListProd h xs -> (ListProd h (Half xs), ListProd h (Half (Tail xs)))
    interleave ListNil = (ListNil, ListNil)
    interleave (ListCons a b0) = case b0 of
      ListCons b rest ->
        let (as, bs) = interleave rest in (ListCons a as, unsafeCoerce $ ListCons b bs)
      ListNil -> (ListCons a ListNil, ListNil)
{-# INLINE[1] fromListProd #-}

toListProd :: h :* k -> ListProd h k
toListProd Nil = ListNil
toListProd (Tree h a0 b0) = ListCons h (unInterleave (toListProd a0) (toListProd b0))
  where
    unInterleave ::
      forall h xs ys. Tail xs ~ ys =>
      ListProd h (Half xs) -> ListProd h (Half ys) -> ListProd h xs
    unInterleave (ListCons a as) bs =
      unsafeCoerce $ ListCons a (unInterleave bs (unsafeCoerce as) :: ListProd h ys)
    unInterleave ListNil _ = unsafeCoerce ListNil
{-# INLINE [1] toListProd #-}

traverseListProd :: Applicative f => (forall x. g x -> f (h x)) -> ListProd g xs -> f (ListProd h xs)
traverseListProd _ ListNil = pure ListNil
traverseListProd f (ListCons a as) = ListCons <$> f a <*> traverseListProd f as

foldMapListProd :: Monoid a => (forall x. g x -> a) -> ListProd g xs -> a
foldMapListProd _ ListNil = mempty
foldMapListProd f (ListCons a as) = f a `mappend` foldMapListProd f as

mapListProd :: (forall x. g x -> h x) -> ListProd g xs -> ListProd h xs
mapListProd _ ListNil = ListNil
mapListProd f (ListCons a as) = f a `ListCons` mapListProd f as

{-# RULES
"fromListProd . toListProd" forall l. fromListProd (toListProd l) = l
"toListProd . fromListProd" forall l. toListProd (fromListProd l) = l
"toListProd . hmap . fromListProd"
    forall (f :: forall x. g x -> h x) l. toListProd (Xu.hmap f (fromListProd l)) = mapListProd f l
 #-}


-- | Map elements to a monoid and combine the results.
--
-- @'hfoldMap' f . 'hmap' g ≡ 'hfoldMap' (f . g)@
hfoldMap :: Monoid a => (forall x. h x -> a) -> h :* xs -> a
hfoldMap f = foldMapListProd f . toListProd
{-# INLINE hfoldMap #-}


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


-- | /O(n)/ Generate a product with the given function.
hgenerate :: (Xu.Generate xs, Applicative f) =>
             (forall x. Membership xs x -> f (h x)) -> f (h :* xs)
hgenerate f = hsequence $ Xu.htabulate (Comp #. f)
{-# INLINE hgenerate #-}


-- | /O(n)/ Analogous to 'hgenerate', but it also supplies a context @c x@ for every elements in @xs@.
hgenerateFor :: (Xu.Forall c xs, Applicative f) => proxy c ->
                (forall x. c x => Membership xs x -> f (h x)) -> f (h :* xs)
hgenerateFor proxy f = hsequence $ Xu.htabulateFor proxy (Comp #. f)
{-# INLINE hgenerateFor #-}

