import LogicLineages.PersistentMarking.NativeTowerOuterIndexConeProof

namespace LogicLineages.PersistentMarking.NativeTowerNestedInnerOrbitLexProof
open Spine NativeIteratorStrictTargets NativeIndexedCarrierTargets
open NativeOrdinalBasisTargets NativeOrdinalBasisChecks NativeOrdinalCapPathsTargets
open NativeIndexedCarrierOrbitBlocksProof NativeTowerIndexedFiniteOrbitProof
open NativeTowerBoundedInnerOrbitBlocksProof NativeTowerOuterIndexConeProof NativeTowerWitnessFamilyProof

/-- Dimension k+1. Coordinates already present are higher-priority; the last
one counts new finite copies of the original literal inner function. -/
def OrbitCoords : Nat → Type
  | 0 => Nat
  | k+1 => OrbitCoords k × Nat

def OrbitLex : (k : Nat) → OrbitCoords k → OrbitCoords k → Prop
  | 0, p, q => Nat.lt p q
  | k+1, p, q => OrbitLex k p.1 q.1 ∨ (p.1 = q.1 ∧ p.2 < q.2)

def nestedPoint (S : Signature) (l : Nat) : (k : Nat) → OrbitCoords k → Base S
  | 0, p => finiteIndex S p
  | k+1, p => originalInnerOrbitBlock S l (nestedPoint S l k p.1) p.2

def nestedCut (S : Signature) (l : Nat) : Nat → Base S
  | 0 => closedOmega S
  | k+1 => evaluatedInner S l (nestedCut S l k)

/-- Add one last-priority coordinate to any already bounded strict index image.
The next bound is the actual evaluated inner carrier at the previous cut. -/
theorem exact_OriginalTowerBoundedOrbitLift (S : Signature) (l : Nat) {I : Type}
    (r : I → I → Prop) (image : I → Base S) (cut : Base S)
    (bounded : ∀ i, NativeBelow (image i) cut)
    (orders : ∀ i j, r i j → NativeBelow (image i) (image j)) :
    (∀ p : I × Nat, NativeBelow (originalInnerOrbitBlock S l (image p.1) p.2)
      (evaluatedInner S l cut)) ∧
    (∀ p q : I × Nat, (r p.1 q.1 ∨ (p.1 = q.1 ∧ p.2 < q.2)) →
      NativeBelow (originalInnerOrbitBlock S l (image p.1) p.2)
        (originalInnerOrbitBlock S l (image q.1) q.2)) := by
  refine ⟨?_,?_⟩
  · intro p
    exact exact_OriginalInnerOrbitIndexCut S l (image p.1) cut (bounded p.1) p.2
  · intro p q smaller
    rcases smaller with first | ⟨same,last⟩
    · exact exact_OriginalInnerOrbitCrossIndex S l _ _ (orders p.1 q.1 first) p.2 q.2
    · rw [congrArg image same]
      exact exact_OriginalInnerOrbitSameIndex S l _ last

theorem exact_OriginalTowerNestedCutAdmitted {S l mapping seed}
    (cone : ActualIndexCone S l mapping seed) (k : Nat) :
    NativeBelow (nestedCut S l k) (actualOuter S mapping seed) := by
  induction k with
  | zero => exact cone.omegaAdmitted
  | succ k ih => exact exact_EvaluatedInnerStaysInActualCone cone (nestedCut S l k) ih

private theorem nestedBoundedStrict (S : Signature) (l k : Nat) :
    (∀ p : OrbitCoords k, NativeBelow (nestedPoint S l k p) (nestedCut S l k)) ∧
    (∀ p q : OrbitCoords k, OrbitLex k p q →
      NativeBelow (nestedPoint S l k p) (nestedPoint S l k q)) := by
  induction k with
  | zero =>
    refine ⟨?_,?_⟩
    · intro p
      have omegaEq : cap (closedSuccessor S) (closedZero S) = closedOmega S := Subtype.ext rfl
      change NativeBelow (finiteIndex S p) (closedOmega S)
      rw [← omegaEq]
      exact (exact_CapAboveFiniteApplications S indexType (closedSuccessor S) (closedZero S) p).2
    · intro p q earlier
      change Nat.lt p q at earlier
      exact exact_SameTypedNativeFiniteOrbitStrict (closedSuccessor S) (closedZero S) earlier
  | succ k ih =>
    exact exact_OriginalTowerBoundedOrbitLift S l (OrbitLex k) (nestedPoint S l k)
      (nestedCut S l k) ih.1 ih.2

theorem exact_OriginalTowerNestedPointBelowCut (S : Signature) (l k : Nat) :
    ∀ p : OrbitCoords k, NativeBelow (nestedPoint S l k p) (nestedCut S l k) :=
  (nestedBoundedStrict S l k).1

theorem exact_OriginalTowerNestedLexPreservation (S : Signature) (l k : Nat) :
    ∀ (p q : OrbitCoords k), OrbitLex k p q →
      NativeBelow (nestedPoint S l k p) (nestedPoint S l k q) :=
  (nestedBoundedStrict S l k).2

/-- Every finite dimensional family is bounded inside the *same* actual
printed t_(l+2). The dimension does not change the outer carrier or its
source map. At each lift the previous point is the actual new index. -/
theorem exact_ActualFixedTowerNestedLex (S : Signature) (l k : Nat) :
    (∀ p : OrbitCoords k, NativeBelow (nestedPoint S l k p) (closedTower S (l+2))) ∧
    (∀ p q : OrbitCoords k, OrbitLex k p q →
      NativeBelow (nestedPoint S l k p) (nestedPoint S l k q)) := by
  obtain ⟨mapping,seed,cone⟩ := exact_ActualOriginalOuterIndexCone S l
  refine ⟨?_,exact_OriginalTowerNestedLexPreservation S l k⟩
  intro p
  have inCone := transBase (exact_OriginalTowerNestedPointBelowCut S l k p)
    (exact_OriginalTowerNestedCutAdmitted cone k)
  exact transBase inCone (positiveRun cone.towerRun (by omega))

def TowerTriple := (Nat × Nat) × Nat

def tripleLex (p q : TowerTriple) : Prop :=
  (p.1.1 < q.1.1 ∨ (p.1.1 = q.1.1 ∧ p.1.2 < q.1.2)) ∨ (p.1 = q.1 ∧ p.2 < q.2)

def tripleImage (S : Signature) (l : Nat) (p : TowerTriple) : Base S :=
  originalInnerOrbitBlock S l (originalInnerOrbitBlock S l (finiteIndex S p.1.1) p.1.2) p.2

theorem exact_ActualFixedTowerTripleLex (S : Signature) (l : Nat) :
    (∀ p, NativeBelow (tripleImage S l p) (closedTower S (l+2))) ∧
    (∀ p q, tripleLex p q → NativeBelow (tripleImage S l p) (tripleImage S l q)) := by
  change (∀ p : OrbitCoords 2, NativeBelow (nestedPoint S l 2 p) (closedTower S (l+2))) ∧
    (∀ p q : OrbitCoords 2, OrbitLex 2 p q → NativeBelow (nestedPoint S l 2 p) (nestedPoint S l 2 q))
  exact exact_ActualFixedTowerNestedLex S l 2

#print axioms exact_OriginalTowerBoundedOrbitLift
#print axioms exact_OriginalTowerNestedCutAdmitted
#print axioms exact_OriginalTowerNestedPointBelowCut
#print axioms exact_OriginalTowerNestedLexPreservation
#print axioms exact_ActualFixedTowerNestedLex
#print axioms exact_ActualFixedTowerTripleLex

end LogicLineages.PersistentMarking.NativeTowerNestedInnerOrbitLexProof
