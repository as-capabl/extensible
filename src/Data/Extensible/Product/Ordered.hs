{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE ViewPatterns, ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE MultiParamTypeClasses, UndecidableInstances #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ScopedTypeVariables #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Extensible.Product
-- Copyright   :  (c) Hidenori Azuma 2015
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

{-
data ListProd (h :: k -> *) (s :: [k]) where
  ListNil :: ListProd h '[]
  ListCons :: !(h x) -> ListProd h xs -> ListProd h (x ': xs)

fromListProd :: ListProd h k -> (h :* k)
fromListProd ListNil = Nil
fromListProd (ListCons x (ListCons y ys)) = undefined

toListProd :: (h :* k) -> ListProd h k
toListProd Nil = ListNil
toListProd (Tree h a b) = ListCons h (unInterleave (toListProd a) (toListProd b))
  where
    unInterleave :: forall h xs. ListProd h (Half xs) -> ListProd h (Half (Tail xs)) -> ListProd h xs
    unInterleave (ListCons a as) bs = ListCons a $ unsafeCoerce $ unInterleave (unsafeCoerce bs) (unsafeCoerce as) :: ListProd h (Tail xs)
    unInterleave ListNil _ = unsafeCoerce ListNil
-}

-- | Map elements to a monoid and combine the results.
--
-- @'hfoldMap' f . 'hmap' g ≡ 'hfoldMap' (f . g)@
hfoldMap :: Monoid a => (forall x. h x -> a) -> h :* xs -> a
hfoldMap _ Nil = mempty
hfoldMap f (Tree h a b) = f h `mappend` hfoldMapHelper f (Seq.fromList [SomeProd a, SomeProd b])
{-# INLINE hfoldMap #-}

data SomeProd h where
  SomeProd :: h :* xs -> SomeProd h

hfoldMapHelper :: Monoid a => (forall x. h x -> a) ->
                   Seq.Seq (SomeProd h) -> a
hfoldMapHelper f (Seq.viewl -> SomeProd Nil :< rest) =
    hfoldMapHelper f rest
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
htraverse f Nil = pure Nil
htraverse f (Tree h a b) =
  (\h' (a', b') -> Tree h' a' b') <$> f h <*> htraverse2 f a b
{-# INLINE htraverse #-}

{-
htraverseHelper :: Applicative f => (forall x. g x -> f (h x)) ->
                   Seq (forall ys. g :* ys) -> f (h :* xs)
htraverseHelper f (viewl -> EmptyL) = Nil
htraverseHelper f (viewl -> Tree h a b Seq.:< rest) =
-}

htraverse2 :: Applicative f => (forall x. g x -> f (h x)) ->
              g :* xs -> g :* ys -> f (h :* xs, h :* ys)
htraverse2 f (Tree h1 a1 b1) (Tree h2 a2 b2) =
  (\h1' h2' (a1', a2') (b1', b2') -> (Tree h1' a1' b1', Tree h2' a2' b2'))
    <$> f h1 <*> f h2 <*> htraverse2 f a1 a2 <*> htraverse2 f b1 b2
htraverse2 f x Nil = (,Nil) <$> htraverse f x
htraverse2 f Nil x = (Nil,) <$> htraverse f x

-- htraverse f (Tree h a b) = Tree <$> f h <*> htraverse f a <*> htraverse f b
-- htraverse _ Nil = pure Nil

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

