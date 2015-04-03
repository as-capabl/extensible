-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Extensible.League
-- Copyright   :  (c) Fumiaki Kinoshita 2015
-- License     :  BSD3
--
-- Maintainer  :  Fumiaki Kinoshita <fumiexcel@gmail.com>
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Pattern matching
------------------------------------------------------------------------
module Data.Extensible.Match (
  matchWith
  , Match(..)
  , _Match
  , match
  , mapMatch
  , caseOf) where

import Data.Extensible.Internal
import Data.Extensible.Internal.Rig
import Data.Extensible.Product
import Data.Extensible.Sum

matchWith :: (forall x. f x -> g x -> r) -> f :* xs -> g :| xs -> r
matchWith f p = \(EmbedAt pos h) -> views (pieceAt pos) f p h
{-# INLINE matchWith #-}

-- | Applies a function to the result of 'Match'.
mapMatch :: (a -> b) -> Match h a x -> Match h b x
mapMatch f (Match g) = Match (f . g)
{-# INLINE mapMatch #-}

-- | /O(log n)/ Perform pattern matching.
match :: Match h a :* xs -> h :| xs -> a
match = matchWith runMatch
{-# INLINE match #-}

-- | Flipped `match`
caseOf :: h :| xs -> Match h a :* xs -> a
caseOf = flip match
{-# INLINE caseOf #-}
infix 0 `caseOf`
