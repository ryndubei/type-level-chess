{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RequiredTypeArguments #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeOperators #-}
module Common.Terminating (type (-|>)(..), TermExpr(..), betaReduce, reduceCase) where

import qualified Control.Category
import Data.Kind
import Data.Type.Equality
import Data.List.Singletons (type (++))

data TermVar (ctx :: [Type]) (t :: Type) where
  TermVarNil :: TermVar (t ': ts) t
  TermVarSucc :: TermVar ts t -> TermVar (t' ': ts) t

data TermLit t where
  TermLitBool :: Bool -> TermLit Bool
  TermLitEq :: (a :~: b) -> TermLit (a :~: b)

type family Lookup (x :: k) (xs :: [(k, v)]) :: Maybe v where
  Lookup k '[] = Nothing
  Lookup k ('(k, v) ': _) = Just v
  Lookup k (_ ': xs) = Lookup k xs

-- | Grammar for a simply-typed lambda calculus with `case` and literals.
--
-- Strict, so either bottom or finite.
data TermExpr (c :: Constraint) (ctx :: [Type]) t where
  TermLamE :: (TermExpr c (ctx ++ '[a]) b) -> (TermExpr c ctx (a -> b))
  TermVarE :: TermVar ctx t -> TermExpr c ctx t
  TermAppE :: TermExpr c ctx (a -> b) -> TermExpr c ctx a -> TermExpr c ctx b
  TermCoerceE :: (c => t ~ t') => TermExpr c ctx t' -> TermExpr c ctx t
  TermLitE :: TermLit t -> TermExpr c ctx t
  TermCaseE :: TermExpr c ctx matchTy -> TermCase c ctx resultTy matchTy -> TermExpr c ctx resultTy

weaken :: TermExpr c ctx t -> TermExpr c (t' ': ctx) t
weaken e = case e of
  TermLamE e' -> TermLamE (weaken e')
  TermVarE x -> TermVarE (TermVarSucc x)
  TermAppE f e' -> TermAppE (weaken f) (weaken e')
  TermCoerceE e' -> TermCoerceE (weaken e')
  TermLitE l -> TermLitE l
  TermCaseE m c -> TermCaseE (weaken m) $ case c of
    TermCaseBool e1 e2 -> TermCaseBool (weaken e1) (weaken e2)
    TermCaseEq e1 -> TermCaseEq (weaken e1)

data TermCase (c :: Constraint) (ctx :: [Type]) (resultTy :: Type) (matchTy :: Type) :: Type where
  TermCaseBool :: TermExpr c ctx result -> TermExpr c ctx result -> TermCase c ctx result Bool
  TermCaseEq :: (TermExpr ((a ~ b), c) ctx result) -> TermCase c ctx result (a :~: b)

constrain :: (c' => c) => TermExpr c ctx t -> TermExpr c' ctx t
constrain e = case e of
  TermLamE e' -> TermLamE (constrain e')
  TermVarE x -> TermVarE x
  TermAppE f e' -> TermAppE (constrain f) (constrain e')
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
    TermLamE e2 -> undefined
    TermAppE f' e2 ->
      let f'' = betaReduce f' e2
       in betaReduce f'' e1
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
  TermCoerceE m' -> reduceCase m' c
  TermLamE _ -> case c of

-- | Terminating function type
newtype a -|> b = TermFn (TermExpr () '[] (a -> b))

instance Control.Category.Category (-|>) where
  id = TermFn $ TermLamE (TermVarE TermVarNil)
  (.) (TermFn f) (TermFn g) =
    TermFn $ TermLamE (TermAppE (weaken f) (TermAppE (weaken g) (TermVarE TermVarNil)))

