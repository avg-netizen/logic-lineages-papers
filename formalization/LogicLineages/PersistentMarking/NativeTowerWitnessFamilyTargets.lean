import LogicLineages.PersistentMarking.NativeTowerExtractorGeneralTargets

namespace LogicLineages.PersistentMarking.NativeTowerWitnessFamilyTargets
open Spine NativeReduction NativeCarrierTargets NativeIndexedCarrierTargets
open NativeOrdinalBasisTargets NativeOrdinalArithmeticTargets NativeTowerExtractorTargets
open NativeTowerWitnessPrefixTargets NativeTowerExtractorGeneralTargets

/-- The full raw prefix consists of the literal printed extractors; no
extractor family or higher typed output is an input. -/
def literalPrefix : (l : Nat) → RawPrefix l
  | 0 => .first (extractor 0)
  | l+1 => .extend (literalPrefix l) (extractor (l+1))

/-- Expand the actual printed decreasing sequence of operands
B_(l−1), …, B₀. The first head is supplied separately as B_l. -/
def printedLower : Nat → Expr → Expr
  | 0, head => head
  | l+1, head => printedLower l (app (ty (l+2)) (ty (l+2)) head (extractor l))

def towerTerm : Nat → Expr
  | 0 => t0
  | 1 => t1
  | l+2 => later (literalPrefix l)

def ExactPrintedNativeTowerSyntax : Prop :=
  towerTerm 0 = t0 ∧ towerTerm 1 = t1 ∧ towerTerm 2 = t2 ∧ towerTerm 3 = t3 ∧
  ∀ l, towerTerm (l+2) = app indexType indexType
    (app endo endo (printedLower l (extractor l)) nativeNB) t0

def ExactClosedNativeTowerFamily : Prop :=
  ∀ (S : Signature) (n : Nat), ClosedNative S (towerTerm n) indexType

/-- The unchanged right operand of the original outer application at
each printed stage, not a comparison with the previous tower height. -/
def finalOperand : Nat → Expr
  | 0 => omegaCarrier
  | _+1 => t0

def ExactNativeTowerFinalOperand : Prop :=
  ∀ (S : Signature) (n : Nat), ClosedNative S (finalOperand n) indexType ∧
    ConfinedPair.Strict S (towerTerm n) (finalOperand n)

end LogicLineages.PersistentMarking.NativeTowerWitnessFamilyTargets
