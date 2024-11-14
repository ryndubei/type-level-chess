{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RequiredTypeArguments #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
module Common.Terminating (type (-|>)(..), TermExpr(..), betaReduce, reduceCase) where

import qualified Control.Category
import GHC.TypeLits
import Data.Kind
import Data.Type.Equality

data TermVar (n :: Symbol) t = TermVar

data TermLit t where
  TermLitBool :: Bool -> TermLit Bool
  TermLitEq :: (a :~: b) -> TermLit (a :~: b)

type TypeContext = [(Symbol, Type)]

type family Lookup (x :: k) (xs :: [(k, v)]) :: Maybe v where
  Lookup k '[] = Nothing
  Lookup k ('(k, v) ': _) = Just v
  Lookup k (_ ': xs) = Lookup k xs

-- | Grammar for a simply-typed lambda calculus with `case` and literals.
--
-- Strict, so either bottom or finite.
data TermExpr (c :: Constraint) (ctx :: TypeContext) t where
  TermLamE :: (Lookup n ctx ~ Nothing) => TermVar n t -> (TermExpr c ('(n, a) ': ctx) b) -> (TermExpr c ctx (a -> b))
  TermVarE :: (Lookup n ctx ~ Just t) => TermVar n t -> TermExpr c ctx t
  TermAppE :: TermExpr c ctx (a -> b) -> TermExpr c ctx a -> TermExpr c ctx b
  TermFreeE :: TermExpr c '[] a -> TermExpr c ctx' a
  TermCoerceE :: (c => t ~ t') => TermExpr c ctx t' -> TermExpr c ctx t
  TermLitE :: TermLit t -> TermExpr c ctx t
  TermCaseE :: TermExpr c ctx matchTy -> TermCase c ctx resultTy matchTy -> TermExpr c ctx resultTy

data TermCase (c :: Constraint) (ctx :: TypeContext) (resultTy :: Type) (matchTy :: Type) :: Type where
  TermCaseBool :: TermExpr c ctx result -> TermExpr c ctx result -> TermCase c ctx result Bool
  TermCaseEq :: (TermExpr ((a ~ b), c) ctx result) -> TermCase c ctx result (a :~: b)

constrain :: (c' => c) => TermExpr c ctx t -> TermExpr c' ctx t
constrain e = case e of
  TermLamE x e' -> TermLamE x (constrain e')
  TermVarE x -> TermVarE x
  TermAppE f e' -> TermAppE (constrain f) (constrain e')
  TermFreeE e' -> TermFreeE (constrain e')
  TermCoerceE e' -> TermCoerceE (constrain e')
  TermLitE l -> TermLitE l
  TermCaseE m c ->
    let c' = case c of
          TermCaseBool e1 e2 -> TermCaseBool (constrain e1) (constrain e2)
          TermCaseEq e1 -> TermCaseEq (constrain e1)
     in TermCaseE (constrain m) c'

betaReduce :: c => TermExpr c '[] (a -> b) -> TermExpr c '[] a -> TermExpr c '[] b
betaReduce f e1 =
  case f of
    TermLamE x e2 -> undefined
    TermAppE f' e2 ->
      let f'' = betaReduce f' e2
       in betaReduce f'' e1
    TermFreeE f' -> betaReduce f' e1
    TermCaseE m c -> betaReduce (reduceCase m c) e1
    TermCoerceE f' -> betaReduce f' e1

reduceCase :: c => TermExpr c '[] matchTy -> TermCase c '[] resultTy matchTy -> TermExpr c '[] resultTy
reduceCase m c = case m of
  TermAppE f' e' ->
    let m' = betaReduce f' e'
     in reduceCase m' c
  TermLitE (TermLitBool True) -> case c of
    TermCaseBool e' _ -> e'
  TermLitE (TermLitBool False) -> case c of
    TermCaseBool _ e' -> e'
  TermLitE (TermLitEq Refl) -> case c of
    TermCaseEq e' -> constrain e'
  TermCaseE m' c' -> reduceCase (reduceCase m' c') c
  TermFreeE m' -> reduceCase m' c
  TermCoerceE m' -> reduceCase m' c
  TermLamE _ _ -> case c of

-- | Terminating function type
newtype a -|> b = TermFn (TermExpr () '[] (a -> b))

instance Control.Category.Category (-|>) where
  id = let x = TermVar @"x" in TermFn $ TermLamE x (TermVarE x)
  (.) (TermFn f) (TermFn g) =
    let x = TermVar @"x"
     in TermFn $ TermLamE x (TermAppE (TermFreeE f) (TermAppE (TermFreeE g) (TermVarE x)))

