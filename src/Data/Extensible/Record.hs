{-# LANGUAGE TemplateHaskell, PolyKinds, TypeFamilies, DataKinds, KindSignatures, FlexibleContexts, FlexibleInstances, FunctionalDependencies, MultiParamTypeClasses, UndecidableInstances, Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Extensible.Record
-- Copyright   :  (c) Fumiaki Kinoshita 2015
-- License     :  BSD3
--
-- Maintainer  :  Fumiaki Kinoshita <fumiexcel@gmail.com>
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Flexible records with well-typed fields.
-- Example: <https://github.com/fumieval/extensible/blob/master/examples/records.hs>
------------------------------------------------------------------------
module Data.Extensible.Record (
   module Data.Extensible.Inclusion
  , Record
  , (<:*)
  , (:*)(Nil)
  , (@=)
  , mkField
  , Field(..)
  , FieldValue
  , FieldLens
  , FieldName
  , Has(..)
  -- * Internal
  , Labelable(..)
  , LabelPhantom
  ) where
import Data.Extensible.Product
import Data.Extensible.Internal
import Language.Haskell.TH
import GHC.TypeLits hiding (Nat)
import Data.Extensible.Inclusion
import Data.Proxy

-- | @FieldLens s@ is a type of lens that points a field named @s@.
--
-- @
-- 'FieldLens' s = (s '∈' xs) => Lens' ('Record' xs) ('FieldValue' s)
-- @
--
type FieldLens a s = forall f p. (Functor f, Labelable s p)
  => p (FieldValue s) (f (FieldValue s)) -> a -> f a

class Has a (s :: Symbol) where
  theLens :: Proxy s -> FieldLens a s

instance (s ∈ xs) => Has (Record xs) s where
  theLens _ f = sector (fmap (Field :: FieldValue s -> Field s) . unlabel (Proxy :: Proxy s) f . getField)

-- | Associates names with concrete types.
type family FieldValue (s :: Symbol) :: *

-- | The type of fields.
data Field (s :: Symbol) = Field { getField :: FieldValue s }

-- | The type of records which contain several fields
type Record = (:*) Field

instance (KnownSymbol s, Show (FieldValue s)) => Show (Field s) where
  showsPrec d f@(Field a) = showParen (d >= 1) $ showString (symbolVal f)
    . showString " @= "
    . showsPrec 1 a

-- | When you see this type as an argument, it expects a 'FieldLens'.
-- This type hooks the name of 'FieldLens' so that an expression @field \@= value@ has no ambiguousity.
type FieldName s = LabelPhantom s (FieldValue s) (Proxy (FieldValue s))
  -> Record '[s] -> Proxy (Record '[s])

-- | A ghostly type used to reify field names
data LabelPhantom s a b

-- | An internal class to characterize 'FieldLens'
class Labelable s p where
  unlabel :: proxy s -> p a b -> a -> b

instance Labelable s (->) where
  unlabel _ = id
  {-# INLINE unlabel #-}

instance (s ~ t) => Labelable s (LabelPhantom t) where
  unlabel _ = error "Impossible"

-- | Annotate a value by the field name.
(@=) :: FieldName s -> FieldValue s -> Field s
(@=) _ = Field
{-# INLINE (@=) #-}
infix 1 @=

-- | Generate a field.
-- @'mkField' "foo" [t|Int|]@ defines:
--
-- @
-- type instance FieldValue "foo" = Int
--
-- foo :: Has "foo" a => FieldLens a "foo"
-- @
--
-- The yielding field is a <http://hackage.haskell.org/package/lens/docs/Control-Lens-Lens.html#t:Lens Lens>.
mkField :: String -> TypeQ -> DecsQ
mkField s t = do
  let a = mkName "a"
  let st = litT (strTyLit s)
  sequence $ [tySynInstD ''FieldValue (tySynEqn [st] t)
    , sigD (mkName s)
      $ forallT [PlainTV a] (sequence [classP ''Has [st, varT a]])
      $ conT ''FieldLens `appT` varT a `appT` st
    , valD (varP $ mkName s) (normalB $ varE 'theLens `appE` sigE (conE 'Proxy) (conT ''Proxy `appT` st)) []
    ]

-- mkStatic :: String -> [String] -> DecsQ
-- mkStatic
