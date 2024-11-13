{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RequiredTypeArguments #-}
module Common.Terminating (type (-|>)(..), TermExpr(..), betaReduce, reduceCase) where

import qualified Control.Category
import GHC.TypeLits
import Data.Kind

newtype TermVar (n :: Symbol) t = TermVar (SSymbol n)

data TermLit t where
  TermLitBool :: Bool -> TermLit Bool

type TypeContext = [(Symbol, Type)]

type family Lookup (x :: k) (xs :: [(k, v)]) :: Maybe v where
  Lookup k '[] = Nothing
  Lookup k ('(k, v) ': _) = Just v
  Lookup k (_ ': xs) = Lookup k xs

-- | Grammar for a simply-typed lambda calculus with `case` and literals.
--
-- Strict, so either bottom or finite.
data TermExpr (ctx :: TypeContext) t where
  TermLamE :: TermVar n t -> (TermExpr ('(n, a) ': ctx) b) -> (TermExpr ctx (a -> b))
  TermVarE :: (Lookup n ctx ~ Just t) => TermVar n t -> TermExpr ctx t
  TermAppE :: TermExpr ctx (a -> b) -> TermExpr ctx a -> TermExpr ctx b
  TermFreeE :: TermExpr '[] a -> TermExpr ctx' a
  TermLitE :: TermLit t -> TermExpr ctx t
  TermCaseE :: TermExpr ctx matchTy -> TermCase ctx resultTy matchTy -> TermExpr ctx resultTy

data TermCase (ctx :: TypeContext) (resultTy :: Type) (matchTy :: Type) :: Type where
  TermCaseBool :: TermExpr ctx result -> TermExpr ctx result -> TermCase ctx result Bool

betaReduce :: forall a b. TermExpr '[] (a -> b) -> TermExpr '[] a -> TermExpr '[] b
betaReduce f e1 =
  case f of
    TermLamE (TermVar n) e2 -> undefined
    TermAppE f' e2 ->
      let f'' = betaReduce f' e2
       in betaReduce f'' e1
    TermFreeE f' -> betaReduce f' e1
    TermCaseE m c -> betaReduce (reduceCase m c) e1

reduceCase :: TermExpr '[] matchTy -> TermCase '[] resultTy matchTy -> TermExpr '[] resultTy
reduceCase m c = case m of
  TermAppE f' e' ->
    let m' = betaReduce f' e'
     in reduceCase m' c
  TermLitE (TermLitBool True) -> case c of
    TermCaseBool e' _ -> e'
  TermLitE (TermLitBool False) -> case c of
    TermCaseBool _ e' -> e'
  TermCaseE m' c' -> reduceCase (reduceCase m' c') c
  TermFreeE m' -> reduceCase m' c
  TermLamE _ _ -> case c of

-- | Terminating function type
newtype a -|> b = TermFn (TermExpr '[] (a -> b))

instance Control.Category.Category (-|>) where
  id = let x = TermVar (SSymbol @"x") in TermFn $ TermLamE x (TermVarE x)
  (.) (TermFn f) (TermFn g) =
    let x = TermVar (SSymbol @"x")
     in TermFn $ TermLamE x (TermAppE (TermFreeE f) (TermAppE (TermFreeE g) (TermVarE x)))

