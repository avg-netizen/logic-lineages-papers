import LogicLineages.PersistentMarking.NativeTowerWitnessFamilyProof

namespace LogicLineages.PersistentMarking.NativeTowerBetaPathTargets
open Spine NativeReduction NativeCarrierTargets NativeIndexedCarrierTargets NativeIteratorStrictTargets
open NativeClosedApplication NativeOrdinalArithmeticTargets NativeOrdinalExponentialTargets
open NativeTowerExtractorTargets NativeTowerExtractorGeneralTargets
open NativeTowerWitnessPrefixTargets NativeTowerWitnessFamilyProof

/-- Original one-binder beta, optionally inside unchanged original
function application slots. The endpoint itself is a closed native term. -/
inductive FunctionBeta (S : Signature) :
    {τ : Ty} → ClosedNativeTerm S τ → ClosedNativeTerm S τ → Prop where
  | root {σ τ : Ty} {body : Expr}
      (typing : ClosedNative S (.lam σ body) (.arrow σ τ))
      (a : ClosedNativeTerm S σ) (out : ClosedNativeTerm S τ)
      (literal : out.val = substitute (.cons a.val .nil) 0 body) :
      FunctionBeta S (applyClosed ⟨.lam σ body,typing⟩ a) out
  | underApp {σ τ : Ty} {before after : ClosedNativeTerm S (.arrow σ τ)}
      (step : FunctionBeta S before after) (arg : ClosedNativeTerm S σ) :
      FunctionBeta S (applyClosed before arg) (applyClosed after arg)

structure BetaStep (S : Signature) {τ : Ty} (before after : ClosedNativeTerm S τ) : Prop where
  beta : FunctionBeta S before after
  reduction : Reduction S before.val after.val
  strict : NativeBelow after before

inductive StrictBetaPath (S : Signature) (τ : Ty) :
    Nat → ClosedNativeTerm S τ → ClosedNativeTerm S τ → Prop where
  | nil (q : ClosedNativeTerm S τ) : StrictBetaPath S τ 0 q q
  | cons {n : Nat} {before middle after : ClosedNativeTerm S τ}
      (one : BetaStep S before middle) (tail : StrictBetaPath S τ n middle after) :
      StrictBetaPath S τ (n+1) before after

/-- The argument at the active original binder of type A_(k+1). For k=0
this is the literal N_B; otherwise it is B_(k−1), not an abstract value. -/
def binderArg : Nat → Expr
  | 0 => nativeNB
  | k+1 => extractor k

/-- All supplied arguments in the nearest-first simultaneous block:
N_B, B₀, …, B_(l−1) when called at (l+1) with []. -/
def consumedArgs : Nat → Args → Args
  | 0, outer => outer
  | k+1, outer => consumedArgs k (.cons (binderArg k) outer)

def extractorFixBody (l : Nat) : Expr := app endo endo ordinalFix (.lam indexType (inner l))

/-- Literal endpoint of just the outer extractor betas. The argument t0
is still installed, and Fix itself has not stepped. -/
def beforeFix (l : Nat) : Expr :=
  app indexType indexType
    (app endo endo ordinalFix (.lam indexType (substitute (consumedArgs (l+1) .nil) 1 (inner l)))) t0

def ExactPrintedTowerBetaPath : Prop :=
  ∀ (S : Signature) (l : Nat),
    ∃ last : ClosedNativeTerm S indexType,
      last.val = beforeFix l ∧ StrictBetaPath S indexType (l+1) (closedTower S (l+2)) last

end LogicLineages.PersistentMarking.NativeTowerBetaPathTargets
