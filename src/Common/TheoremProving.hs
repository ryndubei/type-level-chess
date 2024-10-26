{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
module Common.TheoremProving (exfalso, byContra, doubleNeg) where

import Data.Singletons
import Data.Singletons.Decide
import Data.Void
import Data.Type.Bool
import Data.Bool.Singletons

type family CurryHoward (b :: Bool) where
  CurryHoward 'True = ()
  CurryHoward 'False = Void

exfalso :: ('True :~: 'False) -> a
exfalso r =
  let wts1 :: forall b. ('True :~: b) -> CurryHoward b
      wts1 Refl = ()
      wts2 :: CurryHoward 'False
      wts2 = wts1 r
   in absurd wts2

byContra :: forall p. SingI p => ('True :~: p -> 'True :~: 'False) -> ('False :~: p)
byContra contr = case sing @p of
  STrue -> exfalso $ contr Refl
  SFalse -> Refl

doubleNeg :: forall p. SingI p => (Not (Not p) :~: p)
doubleNeg = case sing @p of
  STrue -> Refl
  SFalse -> Refl
