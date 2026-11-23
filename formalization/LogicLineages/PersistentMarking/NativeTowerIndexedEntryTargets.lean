import LogicLineages.PersistentMarking.NativeTowerBetaPathTargets

namespace LogicLineages.PersistentMarking.NativeTowerIndexedEntryTargets
open Spine NativeReduction NativeIndexedCarrierTargets NativeIteratorStrictTargets
open NativeOrdinalBasisTargets NativeOrdinalArithmeticTargets NativeTowerExtractorGeneralTargets
open NativeTowerWitnessPrefixTargets NativeTowerWitnessFamilyProof NativeTowerBetaPathTargets

def innerMap (l : Nat) : Expr :=
  .lam indexType (substitute (consumedArgs (l+1) .nil) 1 (inner l))

/-- The literal ordinal-successor program applied to t₀, not the
ground successor and not an ordinal abstraction. -/
def successorSeed : Expr := app indexType indexType ordinalSuccessor t0

def indexedEntry (l : Nat) : Expr :=
  indexedW .base (innerMap l) successorSeed omegaCarrier

/-- Indexed chain of original one-step reduction and original confined
strictness at the original type o→o. -/
inductive StrictRun (S : Signature) :
    Nat → ClosedNativeTerm S indexType → ClosedNativeTerm S indexType → Prop where
  | nil (q : ClosedNativeTerm S indexType) : StrictRun S 0 q q
  | cons {n : Nat} {p q r : ClosedNativeTerm S indexType}
      (reduction : Reduction S p.val q.val) (strict : NativeBelow q p)
      (tail : StrictRun S n q r) : StrictRun S (n+1) p r

/-- Exact typed native entry to the printed indexed carrier. No premise
supplies the substituted inner map, its successor seed, or any edge. -/
def ExactNativeTowerIndexedEntry : Prop :=
  ∀ (S : Signature) (l : Nat),
    ∃ (mapping : ClosedNativeTerm S endo) (seed out : ClosedNativeTerm S indexType),
      mapping.val = innerMap l ∧ seed.val = successorSeed ∧ out.val = indexedEntry l ∧
      StrictRun S (l+6) (closedTower S (l+2)) out

end LogicLineages.PersistentMarking.NativeTowerIndexedEntryTargets
