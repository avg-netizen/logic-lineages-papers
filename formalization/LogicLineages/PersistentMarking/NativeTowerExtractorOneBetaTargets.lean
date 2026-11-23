import LogicLineages.PersistentMarking.NativeTowerExtractorTargets

namespace LogicLineages.PersistentMarking.NativeTowerExtractorOneBetaTargets
open Spine NativeReduction NativeCarrierTargets NativeIndexedCarrierTargets
open NativeIteratorTargets NativeIteratorStrictTargets NativeOrdinalBasisTargets
open NativeOrdinalArithmeticTargets NativeOrdinalExponentialTargets NativeTowerExtractorTargets

/-- The actual body after B₁'s first binder is filled; h₁ and α remain. -/
def oneAfterFunction (h : Expr) : Expr := app endo endo ordinalFix
  (.lam indexType (app indexType indexType
    (applied levelOne (.bound indexType 0) h (.bound endo 1)) ordinalZero))

/-- The actual two-binder reduct; α remains and Z is the final operand. -/
def oneResult (h h₁ : Expr) : Expr := app endo endo ordinalFix
  (.lam indexType (app indexType indexType
    (applied levelOne (.bound indexType 0) h h₁) ordinalZero))

def TwoNativeBetaEdges (S : Signature) (start middle last : Expr) : Prop :=
  ∃ p q r : ClosedNativeTerm S endo, p.val = start ∧ q.val = middle ∧ r.val = last ∧
    Reduction S p.val q.val ∧ Reduction S q.val r.val ∧ NativeBelow q p ∧ NativeBelow r q

def NativeExtractorOneOuterBeta : Prop :=
  ∀ S (h : ClosedNativeTerm S levelTwo),
    ∃ start result : ClosedNativeTerm S levelTwo,
      start.val = app levelTwo levelTwo extractorOne h.val ∧
      result.val = .lam endo (oneAfterFunction h.val) ∧
      Reduction S start.val result.val ∧ NativeBelow result start

def NativeExtractorOneBeta : Prop :=
  ∀ S (h : ClosedNativeTerm S levelTwo) (h₁ : ClosedNativeTerm S endo),
    TwoNativeBetaEdges S
      (app endo endo (app levelTwo levelTwo extractorOne h.val) h₁.val)
      (app endo endo (.lam endo (oneAfterFunction h.val)) h₁.val)
      (oneResult h.val h₁.val)

def NativeNBBeta : Prop :=
  ∀ S, TwoNativeBetaEdges S nativeNB
    (app endo endo (.lam endo (oneAfterFunction extractorZero)) ordinalNext)
    (oneResult extractorZero ordinalNext)

end LogicLineages.PersistentMarking.NativeTowerExtractorOneBetaTargets
