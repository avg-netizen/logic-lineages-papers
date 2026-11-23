import LogicLineages.PersistentMarking.NativeOrdinalExponentialTargets

namespace LogicLineages.PersistentMarking.NativeTowerExtractorTargets
open Spine NativeReduction NativeCarrierTargets NativeIndexedCarrierTargets
open NativeIteratorTargets NativeIteratorStrictTargets NativeOrdinalBasisTargets
open NativeOrdinalArithmeticTargets NativeOrdinalExponentialTargets

abbrev levelOne : SemanticType := .arrow .base .base
abbrev levelTwo : Ty := .arrow endo endo
abbrev levelThree : Ty := .arrow levelTwo levelTwo

/-- Literal B₀ inner body, under h then α: It₀ α h Z. -/
def zeroInner : Expr := applied .base (.bound indexType 0) (.bound endo 1) ordinalZero

def zeroBody : Expr := app endo endo ordinalFix (.lam indexType zeroInner)

def extractorZero : Expr := .lam endo zeroBody

def zeroResult (h : Expr) : Expr :=
  app endo endo ordinalFix (.lam indexType (applied .base (.bound indexType 0) h ordinalZero))

/-- Literal B₁ inner body, under h then h₁ then α:
apply the result of (It₁ α h h₁) to the original Z. -/
def oneInner : Expr := app indexType indexType
  (applied levelOne (.bound indexType 0) (.bound levelTwo 2) (.bound endo 1)) ordinalZero

def oneBody : Expr := app endo endo ordinalFix (.lam indexType oneInner)

def extractorOne : Expr := .lam levelTwo (.lam endo oneBody)

/-- The manuscript's left-associated native expression B₁ B₀ Next. -/
def nativeNB : Expr := app endo endo
  (app levelTwo levelTwo extractorOne extractorZero) ordinalNext

def ClosedNativeTowerExtractors : Prop :=
  ∀ S, ClosedNative S extractorZero levelTwo ∧ ClosedNative S extractorOne levelThree ∧
    ClosedNative S nativeNB endo

def NativeTowerExtractorZeroBeta : Prop :=
  ∀ S (h : ClosedNativeTerm S endo),
    ∃ start result : ClosedNativeTerm S endo,
      start.val = app endo endo extractorZero h.val ∧ result.val = zeroResult h.val ∧
      Reduction S start.val result.val ∧ NativeBelow result start

end LogicLineages.PersistentMarking.NativeTowerExtractorTargets
