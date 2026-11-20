import LogicLineages.PersistentMarking.NativeOrdinalArithmeticTargets

namespace LogicLineages.PersistentMarking.NativeOrdinalExponentialTargets
open Spine NativeReduction NativeCarrierTargets NativeIndexedCarrierTargets
open NativeIteratorTargets NativeIteratorStrictTargets NativeOrdinalBasisTargets NativeOrdinalArithmeticTargets

def ordinalOne : Expr := app indexType indexType ordinalSuccessor ordinalZero

def powerStep : Expr := .lam indexType (binaryApplication multiplication (.bound indexType 0) omegaCarrier)

def powerBody : Expr := applied .base (.bound indexType 0) powerStep ordinalOne

def ordinalPower : Expr := .lam indexType powerBody

def fixBody : Expr := .lam indexType
  (applied .base omegaCarrier (.bound endo 1) (app indexType indexType ordinalSuccessor (.bound indexType 0)))

def ordinalFix : Expr := .lam endo fixBody

def ordinalNext : Expr := app endo endo ordinalFix ordinalPower

def powerResult (a : Expr) : Expr := applied .base a powerStep ordinalOne

def fixAfterFunction (f : Expr) : Expr :=
  applied .base omegaCarrier f (app indexType indexType ordinalSuccessor (.bound indexType 0))

def fixResult (f z : Expr) : Expr :=
  applied .base omegaCarrier f (app indexType indexType ordinalSuccessor z)

def ClosedNativeOrdinalExponential : Prop :=
  ∀ S, ClosedNative S ordinalOne indexType ∧ ClosedNative S ordinalPower endo ∧
    ClosedNative S ordinalFix (.arrow endo endo) ∧ ClosedNative S ordinalNext endo

def NativeOrdinalPowerBeta : Prop :=
  ∀ S (a : ClosedNativeTerm S indexType),
    ∃ start result : ClosedNativeTerm S indexType,
      start.val = app indexType indexType ordinalPower a.val ∧
      result.val = powerResult a.val ∧ Reduction S start.val result.val ∧ NativeBelow result start

def FixBetaEdges (S : Signature) (start middle result : Expr) : Prop :=
  ∃ p q r : ClosedNativeTerm S indexType,
    p.val = start ∧ q.val = middle ∧ r.val = result ∧
    Reduction S p.val q.val ∧ Reduction S q.val r.val ∧ NativeBelow q p ∧ NativeBelow r q

def NativeOrdinalFixBeta : Prop :=
  ∀ S (f : ClosedNativeTerm S endo) (z : ClosedNativeTerm S indexType),
    FixBetaEdges S (app indexType indexType (app endo endo ordinalFix f.val) z.val)
      (app indexType indexType (.lam indexType (fixAfterFunction f.val)) z.val) (fixResult f.val z.val)

def NativeOrdinalNextBeta : Prop :=
  ∀ S (z : ClosedNativeTerm S indexType),
    FixBetaEdges S (app indexType indexType ordinalNext z.val)
      (app indexType indexType (.lam indexType (fixAfterFunction ordinalPower)) z.val) (fixResult ordinalPower z.val)

end LogicLineages.PersistentMarking.NativeOrdinalExponentialTargets
