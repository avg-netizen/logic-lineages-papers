import LogicLineages.PersistentMarking.NativeTowerWitnessPrefixTargets

namespace LogicLineages.PersistentMarking.NativeTowerExtractorGeneralTargets
open Spine NativeReduction NativeCarrierTargets NativeIndexedCarrierTargets
open NativeIteratorTargets NativeOrdinalBasisTargets NativeOrdinalArithmeticTargets NativeOrdinalExponentialTargets
open NativeTowerExtractorTargets NativeTowerWitnessPrefixTargets

/-- Under h, h_l, …, h₁, α, depth j stores the actual h_j at A_j.
At the terminal stage there is no h₀: the actual argument is the closed Z. -/
def lowerOperand : Nat → Expr
  | 0 => ordinalZero
  | j+1 => .bound (ty (j+1)) (j+1)

/-- Feed the original ordered suffix h_(k−1),…,h₁,Z to a head at A_k. -/
def drain : Nat → Expr → Expr
  | 0, q => q
  | j+1, q => drain j (app (ty j) (ty j) q (lowerOperand j))

/-- The iterator is the exact original printed native term at level l.
The first argument is α (index 0), the endofunction is h (index l+1),
and its initial state is h_l (or Z when l=0). -/
def inner (l : Nat) : Expr :=
  drain l (applied (level l) (.bound indexType 0) (.bound (ty (l+1)) (l+1)) (lowerOperand l))

/-- Install successive h_j binders from inside to outside. In the final
literal source this is λ h, h_l, …, h₁ (outermost to innermost). -/
def bindAscending : Nat → Nat → Expr → Expr
  | 0, _, q => q
  | n+1, first, q => bindAscending n (first+1) (.lam (ty first) q)

def extractor (l : Nat) : Expr :=
  bindAscending (l+1) 1 (app endo endo ordinalFix (.lam indexType (inner l)))

def ExactGeneralNativeExtractorFamily : Prop :=
  extractor 0 = extractorZero ∧ extractor 1 = extractorOne ∧
  ∀ (S : Signature) (l : Nat), ClosedNative S (extractor l) (ty (l+2))

end LogicLineages.PersistentMarking.NativeTowerExtractorGeneralTargets
