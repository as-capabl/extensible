{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns, BangPatterns #-}
{-# LANGUAGE MagicHash, UnboxedTuples #-}
module Data.Extensible.Struct where

import GHC.Prim
import Control.Monad.Primitive
import Data.Monoid (Sum(..), Endo(..))
import Control.Monad.ST
import Control.Monad
import Data.Extensible.Internal
import GHC.Types

data Struct s (h :: k -> *) (xs :: [k]) = Struct (SmallMutableArray# s Any)

set :: PrimMonad m => Struct (PrimState m) h xs -> Membership xs x -> h x -> m ()
set (Struct m) (getMemberId -> I# i) e = primitive $ \s -> case unsafeCoerce# writeSmallArray# m i e s of
  s' -> (# s', () #)

get :: PrimMonad m => Struct (PrimState m) h xs -> Membership xs x -> m (h x)
get (Struct m) (getMemberId -> I# i) = primitive $ unsafeCoerce# readSmallArray# m i

-- | Given a function that maps types to values, we can "collect" entities all you want.
class Generate (xs :: [k]) where
  -- | /O(n)/ Generate a product with the given function.
  henumerate :: Monoid m => (forall x. Membership xs x -> m) -> m

instance Generate '[] where
  henumerate _ = mempty
  {-# INLINE henumerate #-}

instance Generate xs => Generate (x ': xs) where
  henumerate f = f here `mappend` henumerate (f . navNext)
  {-# INLINE henumerate #-}

new :: forall h m xs. (PrimMonad m, Generate xs) => (forall x. Membership xs x -> h x) -> m (Struct (PrimState m) h xs)
new k = do
  let !(Sum (I# n)) = henumerate (const (Sum 1) :: Membership xs x -> Sum Int)
  m <- primitive $ \s -> case newSmallArray# n undefined s of
    (# s', a #) -> (# s', Struct a #)
  let Endo r = henumerate ((\i -> Endo (set m i (k i)>>)) :: Membership xs x -> Endo (m (Struct (PrimState m) h xs)))
  r (return m)

-- | The type of extensible products.
--
-- @(:*) :: (k -> *) -> [k] -> *@
--
data (h :: k -> *) :* (s :: [k]) = HProduct (SmallArray# Any)

unsafeFreeze :: PrimMonad m => Struct (PrimState m) h xs -> m (h :* xs)
unsafeFreeze (Struct m) = primitive $ \s -> case unsafeFreezeSmallArray# m s of
  (# s', a #) -> (# s', HProduct a #)

newFrom :: forall g h m xs. (PrimMonad m)
  => g :* xs
  -> (forall x. Membership xs x -> g x -> h x)
  -> m (Struct (PrimState m) h xs)
newFrom p@(HProduct ar) k = do
  Struct m <- primitive $ \s -> case newSmallArray# (sizeofSmallArray# ar) undefined s of
    (# s', a #) -> (# s', Struct a #)
  forM_ [0..I# (sizeofSmallArray# ar) - 1] $ \(I# i) -> primitive $ \s -> unsafeCoerce# writeSmallArray# m i
    (unsafeCoerce# k i (indexSmallArray# ar i))
    s
  return (Struct m)

hlookup :: Membership xs x -> h :* xs -> h x
hlookup = flip hindex
{-# INLINE hlookup #-}

hindex :: h :* xs -> Membership xs x -> h x
hindex (HProduct ar) (getMemberId -> I# i) = case indexSmallArray# ar i of
  (# a #) -> unsafeCoerce# a
{-# INLINE hindex #-}

hmap :: (forall x. g x -> h x) -> g :* xs -> h :* xs
hmap t p = runST $ newFrom p (const t) >>= unsafeFreeze

hmapWithIndex :: (forall x. Membership xs x -> g x -> h x) -> g :* xs -> h :* xs
hmapWithIndex t p = runST $ newFrom p t >>= unsafeFreeze