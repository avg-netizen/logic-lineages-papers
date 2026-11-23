import LogicLineages.PersistentMarking.NativeOrdinalCapAbstractionProof
import LogicLineages.PersistentMarking.NativeOrdinalCapPathsTargets
import LogicLineages.PersistentMarking.StablePairProof

namespace LogicLineages.PersistentMarking.NativeOrdinalCapHierarchyBoundsProof
open Spine NativeIndexedCarrierTargets NativeIteratorStrictTargets NativeClosedApplication
open NativeOrdinalBasisTargets NativeOrdinalBasisChecks NativeOrdinalCapPathsTargets
open NativeOrdinalCapAbstractionProof

abbrev BaseTerm (S : Signature) := ClosedNativeTerm S indexType
abbrev EndoTerm (S : Signature) := ClosedNativeTerm S (.arrow indexType indexType)

/-- Each new level abstracts the genuine cap with the previous level as step. -/
def capLevel (S : Signature) : Nat → EndoTerm S
  | 0 => closedSuccessor S
  | d + 1 => capEndo (capLevel S d)

/-- Outer coordinate is the one interpreted at the highest remaining level. -/
def Coordinates : Nat → Type
  | 0 => Unit
  | d + 1 => Nat × Coordinates d

def blockAt (S : Signature) : (d : Nat) → Coordinates d → BaseTerm S → BaseTerm S
  | 0, _, u => u
  | d + 1, p, u => blockAt S d p.2 (finiteApplication (capLevel S d) u p.1)

def NativeLe {S} (u v : BaseTerm S) : Prop := u = v ∨ NativeBelow u v

theorem strictComp {S} {u v w : BaseTerm S} (uv : NativeBelow u v)
    (vw : NativeBelow v w) : NativeBelow u w :=
  StablePairProof.strictTransitive S w.val v.val u.val vw uv

theorem leStrict {S} {u v w : BaseTerm S} (uv : NativeLe u v)
    (vw : NativeBelow v w) : NativeBelow u w := by
  rcases uv with eq | uv
  · rwa [eq]
  · exact strictComp uv vw

theorem strictLe {S} {u v w : BaseTerm S} (uv : NativeBelow u v)
    (vw : NativeLe v w) : NativeBelow u w := by
  rcases vw with eq | vw
  · rwa [← eq]
  · exact strictComp uv vw

theorem leComp {S} {u v w : BaseTerm S} (uv : NativeLe u v)
    (vw : NativeLe v w) : NativeLe u w := by
  rcases uv with eq | uv
  · rwa [eq]
  · exact Or.inr (strictLe uv vw)

/-- Actual cap then actual beta strictly dominates each finite application below. -/
theorem exact_CapLevelIterationCeiling (S : Signature) (d : Nat) (u : BaseTerm S) (m : Nat) :
    NativeBelow (finiteApplication (capLevel S d) u m) (applyClosed (capLevel S (d+1)) u) :=
  strictComp (exact_CapAboveFiniteApplications S indexType (capLevel S d) u m).2
    (exact_NativeCapAbstractionBeta (capLevel S d) u).2.2

theorem levelRaises (S : Signature) (d : Nat) (u : BaseTerm S) :
    NativeBelow u (applyClosed (capLevel S d) u) := by
  cases d with
  | zero =>
    obtain ⟨start,mid,lit,_,_,first,second⟩ := exact_OrdinalSuccessorSteps S u
    have eq : start = applyClosed (capLevel S 0) u := Subtype.ext lit
    rw [← eq]
    exact strictComp second first
  | succ d => exact exact_CapLevelIterationCeiling S d u 0

theorem iterationLe (S : Signature) (d : Nat) (u : BaseTerm S) {m n : Nat} (h : m ≤ n) :
    NativeLe (finiteApplication (capLevel S d) u m) (finiteApplication (capLevel S d) u n) := by
  induction h with
  | refl => exact Or.inl rfl
  | @step k _ ih =>
    exact Or.inr (leStrict ih (levelRaises S d (finiteApplication (capLevel S d) u k)))

theorem exact_CapHierarchyFloorCeiling (S : Signature) (d : Nat) :
    ∀ (p : Coordinates d) (u : BaseTerm S),
      NativeLe u (blockAt S d p u) ∧ NativeBelow (blockAt S d p u) (applyClosed (capLevel S d) u) := by
  induction d with
  | zero =>
    intro p u
    exact ⟨Or.inl rfl,levelRaises S 0 u⟩
  | succ d ih =>
    intro p u
    let v := finiteApplication (capLevel S d) u p.1
    have lower := ih p.2 v
    have front : NativeLe u v := iterationLe S d u (Nat.zero_le p.1)
    have paid : NativeBelow (blockAt S d p.2 v)
        (finiteApplication (capLevel S d) u (p.1+1)) := lower.2
    exact ⟨leComp front lower.1,strictComp paid
      (exact_CapLevelIterationCeiling S d u (p.1+1))⟩

#print axioms exact_CapLevelIterationCeiling
#print axioms exact_CapHierarchyFloorCeiling

end LogicLineages.PersistentMarking.NativeOrdinalCapHierarchyBoundsProof
