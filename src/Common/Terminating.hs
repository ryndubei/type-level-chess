{-# LANGUAGE StrictData #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RequiredTypeArguments #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
module Common.Terminating
  ( TermExpr(..)
  , TermVar(..)
  , TermLiteral(..)
  , IsFunction
  , TermExprArgs
  , evaluate
  , constrain
  , weakenLeft
  , weakenRight
  , weaken
  ) where

import Data.Kind
import Data.Type.Equality
import Data.Type.Bool (If)
import Data.Void

type family IsFunction (t :: Type) :: Bool where
  IsFunction (a -> b) = 'True
  IsFunction _ = 'False

type family TermExprArgs (lits :: Type -> Type) (c :: Constraint) (f :: Type) :: Type where
  TermExprArgs lits c (a -> b) = TermExpr lits c '[] a -> If (IsFunction b) (TermExprArgs lits c b) b

class TermLiteral (lit :: Type -> Type) where
  data TermCase lit (c :: Constraint) (ctx :: [Type]) resultTy t
  noFunctionCase :: TermCase lit c ctx resultTy (a -> b) -> Void
  noFunctionLits :: lit t -> IsFunction t :~: 'False
  existsCase :: lit t -> TermCase lit () '[] t t
  reduceCaseLit :: lit t -> TermCase lit c '[] resultTy t -> TermExpr lit c '[] resultTy
  evaluateLit :: lit t -> t
  traverseCase :: (TermExpr lit c ctx t -> TermExpr lit c' ctx' t) -> TermCase lit c ctx resultTy t -> TermCase lit c' ctx' resultTy t

-- | Reversed de Bruijin indices: 'TermVarNil' is the most recent bound variable
data TermVar (ctx :: [Type]) (t :: Type) where
  TermVarNil :: TermVar (t ': ts) t
  TermVarSucc :: TermVar ts t -> TermVar (t' ': ts) t

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
data TermExpr (lits :: Type -> Type) (c :: Constraint) (ctx :: [Type]) t where
  TermLamE :: TermExpr lits c (a ': ctx) b -> TermExpr lits c ctx (a -> b)
  TermVarE :: TermVar ctx t -> TermExpr lits c ctx t
  TermAppE :: TermExpr lits c ctx (a -> b) -> TermExpr lits c ctx a -> TermExpr lits c ctx b
  TermCoerceE :: (c => t ~ t') => TermExpr lits c ctx t' -> TermExpr lits c ctx t
  TermLitE :: lits t -> TermExpr lits c ctx t
  TermCaseE :: TermExpr lits c ctx matchTy -> TermCase lits c ctx resultTy matchTy -> TermExpr lits c ctx resultTy

revar :: forall t' -> TermVar ctx t -> TermVar (ctx ++ '[t']) t
revar _ TermVarNil = TermVarNil
revar t' (TermVarSucc x) = TermVarSucc (revar t' x)

weakenRight :: TermLiteral lits => forall t' -> TermExpr lits c ctx t -> TermExpr lits c (ctx ++ '[t']) t
weakenRight t' e = case e of
  TermLamE e' -> TermLamE (weakenRight t' e')
  TermVarE x -> TermVarE (revar t' x)
  TermAppE f e' -> TermAppE (weakenRight t' f) (weakenRight t' e')
  TermCoerceE e' -> TermCoerceE (weakenRight t' e')
  TermLitE l -> TermLitE l
  TermCaseE m c -> TermCaseE (weakenRight t' m) (traverseCase (weakenRight t') c)

weakenLeft :: forall c ctx t t' lits. TermLiteral lits => TermExpr lits c ctx t -> TermExpr lits c (t' ': ctx) t
weakenLeft = weaken ctx t' LengthNil

weaken :: forall ctx1 c t lits. TermLiteral lits => forall ctx2 t' -> Length ctx1 -> TermExpr lits c (ctx1 ++ ctx2) t -> TermExpr lits c (ctx1 ++ (t' ': ctx2)) t
weaken ctx2 t' len e = case e of
  TermLamE e' -> TermLamE (weaken ctx2 t' (LengthSucc len) e')
  TermVarE x -> TermVarE (weakenVar len x)
  TermAppE f e' -> TermAppE (weaken ctx2 t' len f) (weaken ctx2 t' len e')
  TermCoerceE e' -> TermCoerceE (weaken ctx2 t' len e')
  TermLitE l -> TermLitE l
  TermCaseE m c -> TermCaseE (weaken ctx2 t' len m) (traverseCase (weaken ctx2 t' len) c)
  where
    weakenVar :: forall ctx1'. Length ctx1' -> TermVar (ctx1' ++ ctx2) t -> TermVar (ctx1' ++ (t' ': ctx2)) t
    weakenVar LengthNil x = TermVarSucc x
    weakenVar (LengthSucc _) TermVarNil = TermVarNil
    weakenVar (LengthSucc l) (TermVarSucc x) = TermVarSucc (weakenVar l x)
 
substitute' :: forall ctx1 c et lits. TermLiteral lits => forall ctx2 t -> Length ctx1 -> TermExpr lits c (ctx1 ++ (t ': ctx2)) et -> TermExpr lits c ctx2 t -> TermExpr lits c (ctx1 ++ ctx2) et
substitute' ctx2 t len e se = case e of
  TermLamE e' -> TermLamE (substitute' ctx2 t (LengthSucc len) e' se)
  TermVarE x -> strengthenVar len se x
  TermAppE f e' -> TermAppE (substitute' ctx2 t len f se) (substitute' ctx2 t len e' se)
  TermCoerceE e' -> TermCoerceE (substitute' ctx2 t len e' se)
  TermLitE l -> TermLitE l
  TermCaseE m c -> TermCaseE (substitute' ctx2 t len m se) (traverseCase (\cc -> substitute' ctx2 t len cc se) c)
  where
    strengthenVar :: forall ctx1' vt. Length ctx1' -> TermExpr lits c ctx2 t -> TermVar (ctx1' ++ (t ': ctx2)) vt -> TermExpr lits c (ctx1' ++ ctx2) vt
    strengthenVar LengthNil s TermVarNil = s
    strengthenVar LengthNil _ (TermVarSucc x) = TermVarE x
    strengthenVar (LengthSucc _) _ TermVarNil = TermVarE TermVarNil
    strengthenVar (LengthSucc l) s (TermVarSucc x) = weakenLeft $ strengthenVar l s x

substitute :: forall c t ctx et lits. TermLiteral lits => TermExpr lits c (t ': ctx) et -> TermExpr lits c ctx t -> TermExpr lits c ctx et
substitute e se =
  let e' = constrain e
      se' = constrain se
   in substitute' ctx t LengthNil e' se'

constrain :: (c' => c, TermLiteral lits) => TermExpr lits c ctx t -> TermExpr lits c' ctx t
constrain e = case e of
  TermLamE e' -> TermLamE (constrain e')
  TermVarE x -> TermVarE x
  TermAppE f e' -> TermAppE (constrain f) (constrain e')
  TermCoerceE e' -> TermCoerceE (constrain e')
  TermLitE l -> TermLitE l
  TermCaseE m c ->
    let c' = traverseCase constrain c
     in TermCaseE (constrain m) c'

betaReduce :: forall c a b lits. TermLiteral lits => c => TermExpr lits c '[] (a -> b) -> TermExpr lits c '[] a -> TermExpr lits c '[] b
betaReduce f e1 =
  case f of
    TermLamE e2 -> substitute e2 e1
    TermAppE f' e2 ->
      let f'' = betaReduce f' e2
       in betaReduce f'' e1
    TermCaseE m c -> betaReduce (reduceCase m c) e1
    TermCoerceE f' -> betaReduce f' e1
    TermLitE l -> absurd $ noFunctionCase (existsCase l)

evaluate :: forall c t lits. (c, TermLiteral lits) => TermExpr lits c '[] t -> If (IsFunction t) (TermExprArgs lits c t) t
evaluate (TermLitE l) = case noFunctionLits l of Refl -> evaluateLit l
evaluate (TermAppE f e) = evaluate (betaReduce f e)
evaluate (TermCoerceE (e :: TermExpr lits c '[] t')) =
  case (Refl :: t :~: t') of Refl -> evaluate e
evaluate (TermCaseE m c) = evaluate (reduceCase m c)
evaluate (TermLamE e) = \se -> evaluate (substitute e se)

reduceCase :: forall c lits matchTy resultTy.
              (c, TermLiteral lits)
           => TermExpr lits c '[] matchTy
           -> TermCase lits c '[] resultTy matchTy
           -> TermExpr lits c '[] resultTy
reduceCase m c = case m of
  TermAppE f' e' ->
    let m' = betaReduce f' e'
     in reduceCase m' c
  TermLitE l -> reduceCaseLit l c
  TermCaseE m' c' -> reduceCase (reduceCase m' c') c
  TermCoerceE (m' :: TermExpr lits c '[] matchTy') ->
    case (Refl :: matchTy :~: matchTy') of Refl -> reduceCase m' c
  TermLamE _ -> absurd $ noFunctionCase c
