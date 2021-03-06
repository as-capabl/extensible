{-# LANGUAGE LambdaCase, TemplateHaskell, TypeFamilies, DeriveFunctor #-}
module Data.Extensible.Record (IsRecord(..), deriveIsRecord) where

import Language.Haskell.TH
import Data.Extensible.Internal
import Data.Extensible.Product
import Data.Extensible.Field
import Data.Functor.Identity
import GHC.TypeLits

-- | The class of types that can be converted to/from a 'Record'.
class IsRecord a where
  type RecFields a :: [Assoc Symbol *]
  fromRecord :: Record (RecFields a) -> a
  toRecord :: a -> Record (RecFields a)

tvName :: TyVarBndr -> Name
tvName (PlainTV n) = n
tvName (KindedTV n _) = n

deriveIsRecord :: Name -> DecsQ
deriveIsRecord name = reify name >>= \case
#if MIN_VERSION_template_haskell(2,11,0)
  TyConI (DataD _ _ vars _ [RecC conName vst] _) -> do
#else
  TyConI (DataD _ _ vars [RecC conName vst] _) -> do
#endif
    rec <- newName "rec"
    let names = [x | (x, _, _) <- vst]
    newNames <- traverse (newName . nameBase) names
    let tvmap = [(tvName tv, VarT (mkName $ "p" ++ show i)) | (i, tv) <- zip [0 :: Int ..] vars]
    let ty = foldl AppT (ConT name) $ map snd tvmap
    let refineTV (VarT t) | Just t' <- lookup t tvmap = t'
        refineTV (AppT a b) = refineTV a `AppT` refineTV b
        refineTV t = t
    return
#if MIN_VERSION_template_haskell(2,11,0)
      [InstanceD Nothing [] (ConT ''IsRecord `AppT` ty)
#else
      [InstanceD [] (ConT ''IsRecord `AppT` ty)
#endif
        [ TySynInstD ''RecFields $ TySynEqn [ty] $ foldr
            (\(v, _, t) r -> PromotedConsT `AppT` (PromotedT '(:>) `AppT` LitT (StrTyLit $ nameBase v) `AppT` refineTV t) `AppT` r)
            PromotedNilT
            vst
        , FunD 'fromRecord [Clause
            [shape2Pat $ fmap (\x -> ConP 'Field [ConP 'Identity [VarP x]]) $ foldr consShape SNil newNames]
            (NormalB $ RecConE conName [(n, VarE n') | (n, n') <- zip names newNames])
            []
            ]
        , FunD 'toRecord [Clause
            [VarP rec]
            (NormalB $ shape2Exp
              $ foldr consShape SNil
              [AppE (ConE 'Field)
                $ AppE (ConE 'Identity)
                $ VarE n `AppE` VarE rec
              | n <- names])
            []
            ]
        ]
      ]
  info -> fail $ "deriveAsRecord: Unsupported " ++ show info

shape2Pat :: Shape Pat -> Pat
shape2Pat SNil = ConP 'Nil []
shape2Pat (STree p l r) = ConP 'Tree [p, shape2Pat l, shape2Pat r]

shape2Exp :: Shape Exp -> Exp
shape2Exp SNil = ConE 'Nil
shape2Exp (STree e l r) = ConE 'Tree `AppE` e `AppE` shape2Exp l `AppE` shape2Exp r

data Shape a = SNil
    | STree a (Shape a) (Shape a)
    deriving Functor

consShape :: a -> Shape a -> Shape a
consShape a SNil = STree a SNil SNil
consShape a (STree b l r) = STree a (consShape b r) l
