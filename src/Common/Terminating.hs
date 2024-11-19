{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RequiredTypeArguments #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeOperators #-}
module Common.Terminating (type (-|>)(..), TermExpr(..), TermExprArgs, evaluate, constrain) where

import qualified Control.Category
import Data.Kind
import Data.Type.Equality
import Data.List.Singletons (type (++))

-- | Reversed de Bruijin indices: 'TermVarNil' is the most recent bound variable
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

type family (++) (xs :: [k]) (ys :: [k]) :: [k] where
  '[] ++ ys = ys
  (x ': xs) ++ ys = x ': (xs ++ ys)

data Length (xs :: [k]) where
  LengthNil :: Length '[]
  LengthSucc :: Length xs -> Length (x ': xs)

-- | Grammar for a simply-typed lambda calculus with `case` and literals.
--
-- Strict, so either bottom or finite.
data TermExpr (c :: Constraint) (ctx :: [Type]) t where
  TermLamE :: TermExpr c (a ': ctx) b -> TermExpr c ctx (a -> b)
  TermVarE :: TermVar ctx t -> TermExpr c ctx t
  TermAppE :: TermExpr c ctx (a -> b) -> TermExpr c ctx a -> TermExpr c ctx b
  TermCoerceE :: (c => t ~ t') => TermExpr c ctx t' -> TermExpr c ctx t
  TermLitE :: TermLit t -> TermExpr c ctx t
  TermCaseE :: TermExpr c ctx matchTy -> TermCase c ctx resultTy matchTy -> TermExpr c ctx resultTy

revar :: forall t' -> TermVar ctx t -> TermVar (ctx ++ '[t']) t
revar _ TermVarNil = TermVarNil
revar t' (TermVarSucc x) = TermVarSucc (revar t' x)

weakenRight :: forall t' -> TermExpr c ctx t -> TermExpr c (ctx ++ '[t']) t
weakenRight t' e = case e of
  TermLamE e' -> TermLamE (weakenRight t' e')
  TermVarE x -> TermVarE (revar t' x)
  TermAppE f e' -> TermAppE (weakenRight t' f) (weakenRight t' e')
  TermCoerceE e' -> TermCoerceE (weakenRight t' e')
  TermLitE l -> TermLitE l
  TermCaseE m c -> TermCaseE (weakenRight t' m) $ case c of
    TermCaseBool e1 e2 -> TermCaseBool (weakenRight t' e1) (weakenRight t' e2)
    TermCaseEq e1 -> TermCaseEq (weakenRight t' e1)

weakenLeft :: forall c ctx t t'. TermExpr c ctx t -> TermExpr c (t' ': ctx) t
weakenLeft = weaken ctx t' LengthNil

weaken :: forall ctx1 c t. forall ctx2 t' -> Length ctx1 -> TermExpr c (ctx1 ++ ctx2) t -> TermExpr c (ctx1 ++ (t' ': ctx2)) t
weaken ctx2 t' len e = case e of
  TermLamE e' -> TermLamE (weaken ctx2 t' (LengthSucc len) e')
  TermVarE x -> TermVarE (weakenVar len x)
  TermAppE f e' -> TermAppE (weaken ctx2 t' len f) (weaken ctx2 t' len e')
  TermCoerceE e' -> TermCoerceE (weaken ctx2 t' len e')
  TermLitE l -> TermLitE l
  TermCaseE m c -> TermCaseE (weaken ctx2 t' len m) $ case c of
    TermCaseBool e1 e2 -> TermCaseBool (weaken ctx2 t' len e1) (weaken ctx2 t' len e2)
    TermCaseEq e1 -> TermCaseEq (weaken ctx2 t' len e1)
  where
    weakenVar :: forall ctx1'. Length ctx1' -> TermVar (ctx1' ++ ctx2) t -> TermVar (ctx1' ++ (t' ': ctx2)) t
    weakenVar LengthNil x = TermVarSucc x
    weakenVar (LengthSucc _) TermVarNil = TermVarNil
    weakenVar (LengthSucc l) (TermVarSucc x) = TermVarSucc (weakenVar l x)
 
substitute' :: forall ctx1 c et. forall ctx2 t -> Length ctx1 -> TermExpr c (ctx1 ++ (t ': ctx2)) et -> TermExpr c ctx2 t -> TermExpr c (ctx1 ++ ctx2) et
substitute' ctx2 t len e se = case e of
  TermLamE e' -> TermLamE (substitute' ctx2 t (LengthSucc len) e' se)
  TermVarE x -> strengthenVar len se x
  TermAppE f e' -> TermAppE (substitute' ctx2 t len f se) (substitute' ctx2 t len e' se)
  TermCoerceE e' -> TermCoerceE (substitute' ctx2 t len e' se)
  TermLitE l -> TermLitE l
  TermCaseE m c -> TermCaseE (substitute' ctx2 t len m se) $ case c of
    TermCaseBool e1 e2 -> TermCaseBool (substitute' ctx2 t len e1 se) (substitute' ctx2 t len e2 se)
    TermCaseEq e1 -> TermCaseEq (substitute' ctx2 t len e1 (constrain se))
  where
    strengthenVar :: forall ctx1' vt. Length ctx1' -> TermExpr c ctx2 t -> TermVar (ctx1' ++ (t ': ctx2)) vt -> TermExpr c (ctx1' ++ ctx2) vt
    strengthenVar LengthNil s TermVarNil = s
    strengthenVar LengthNil _ (TermVarSucc x) = TermVarE x
    strengthenVar (LengthSucc _) _ TermVarNil = TermVarE TermVarNil
    strengthenVar (LengthSucc l) s (TermVarSucc x) = weakenLeft $ strengthenVar l s x

substitute :: forall c t ctx et. TermExpr c (t ': ctx) et -> TermExpr c ctx t -> TermExpr c ctx et
substitute e se =
  let e' = constrain e
      se' = constrain se
   in substitute' ctx t LengthNil e' se'

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
    TermLamE e2 -> substitute e2 e1
    TermAppE f' e2 ->
      let f'' = betaReduce f' e2
       in betaReduce f'' e1
    TermCaseE m c -> betaReduce (reduceCase m c) e1
    TermCoerceE f' -> betaReduce f' e1

type family TermExprArgs c (f :: Type) :: Type where
  TermExprArgs c (a -> b) = TermExpr c '[] a -> TermExprArgs c b
  TermExprArgs c a = a

evaluate :: forall c t. c => TermExpr c '[] t -> TermExprArgs c t
evaluate (TermLitE l) = case l of
  TermLitBool b -> b
  TermLitEq Refl -> Refl
evaluate (TermAppE f e) = evaluate (betaReduce f e)
evaluate (TermCoerceE (e :: TermExpr c '[] t')) =
  case (Refl :: t :~: t') of Refl -> evaluate e
evaluate (TermCaseE m c) = evaluate (reduceCase m c)
evaluate (TermLamE e) = \se -> evaluate (substitute e se)

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
    TermFn $ TermLamE (TermAppE (weakenRight _ f) (TermAppE (weakenRight _ g) (TermVarE TermVarNil)))

