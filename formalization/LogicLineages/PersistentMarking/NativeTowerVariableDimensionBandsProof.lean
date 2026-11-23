import LogicLineages.PersistentMarking.NativeTowerIncreasingInnerCutsProof
import LogicLineages.PersistentMarking.NativeTowerNestedInnerOrbitLexProof

namespace LogicLineages.PersistentMarking.NativeTowerVariableDimensionBandsProof
open Spine NativeIteratorStrictTargets NativeTowerWitnessFamilyProof
open NativeTowerOuterIndexConeProof NativeTowerNestedInnerOrbitLexProof
open NativeTowerBoundedInnerOrbitBlocksProof NativeTowerIncreasingInnerCutsProof

def anchoredPoint (S : Signature) (l : Nat) (a : Base S) : (d : Nat) → OrbitCoords d → Base S
  | 0, p => originalInnerOrbitBlock S l a p
  | d+1, p => originalInnerOrbitBlock S l (anchoredPoint S l a d p.1) p.2

theorem exact_OriginalAnchoredBand (S : Signature) (l : Nat) (a : Base S)
    (starts : NativeBelow a (evaluatedInner S l a)) (d : Nat) :
    (∀ p : OrbitCoords d, NativeBelow a (anchoredPoint S l a d p)) ∧
    (∀ p : OrbitCoords d, NativeBelow (anchoredPoint S l a d p) (evaluatedCutIter S l a (d+2))) ∧
    (∀ p q : OrbitCoords d, OrbitLex d p q →
      NativeBelow (anchoredPoint S l a d p) (anchoredPoint S l a d q)) := by
  induction d with
  | zero =>
    refine ⟨?_,?_,?_⟩
    · intro p
      change NativeBelow a (originalInnerOrbitBlock S l a p)
      cases p with
      | zero => exact starts
      | succ p =>
        exact transBase starts (exact_OriginalInnerOrbitSameIndex S l a (Nat.zero_lt_succ p))
    · intro p
      exact exact_OriginalInnerOrbitIndexCut S l a (evaluatedInner S l a) starts p
    · intro p q earlier
      change Nat.lt p q at earlier
      exact exact_OriginalInnerOrbitSameIndex S l a earlier
  | succ d ih =>
    have lifted := exact_OriginalTowerBoundedOrbitLift S l (OrbitLex d)
      (anchoredPoint S l a d) (evaluatedCutIter S l a (d+2)) ih.2.1 ih.2.2
    refine ⟨?_,lifted.1,lifted.2⟩
    intro p
    have above := exact_OriginalInnerOrbitCrossIndex S l a
      (anchoredPoint S l a d p.1) (ih.1 p.1) 0 p.2
    exact transBase starts above

def bandPoint (S : Signature) (l d : Nat) (p : OrbitCoords d) : Base S :=
  anchoredPoint S l (bandStart S l d) d p

theorem exact_OriginalTowerBandEndpoints (S : Signature) (l d : Nat) (p : OrbitCoords d) :
    NativeBelow (bandStart S l d) (bandPoint S l d p) ∧
      NativeBelow (bandPoint S l d p) (bandStart S l (d+1)) := by
  have h := exact_OriginalAnchoredBand S l (bandStart S l d) (exact_OriginalBandStartRises S l d) d
  exact ⟨h.1 p,h.2.1 p⟩

theorem exact_OriginalTowerBandSeparation (S : Signature) (l d e : Nat)
    (p : OrbitCoords d) (q : OrbitCoords e) (later : d < e) :
    NativeBelow (bandPoint S l d p) (bandPoint S l e q) := by
  have before := (exact_OriginalTowerBandEndpoints S l d p).2
  have after := (exact_OriginalTowerBandEndpoints S l e q).1
  rcases exact_OriginalBandStartsWeaklyOrdered S l (show d+1 ≤ e from later) with same | between
  · rw [same] at before
    exact transBase before after
  · exact transBase (transBase before between) after

/-- One actual sum of increasing variable-dimensional lex bands. The Sigma
retains the original dimension and its exact type of inner coordinates. -/
def BandCoords := Σ d : Nat, OrbitCoords d

def BandLex (p q : BandCoords) : Prop :=
  p.1 < q.1 ∨ ∃ same : p.1 = q.1,
    OrbitLex p.1 p.2 (cast (congrArg OrbitCoords same.symm) q.2)

def bandImage (S : Signature) (l : Nat) (p : BandCoords) : Base S :=
  bandPoint S l p.1 p.2

theorem exact_OriginalTowerBandLexPreservation (S : Signature) (l : Nat) (p q : BandCoords)
    (smaller : BandLex p q) : NativeBelow (bandImage S l p) (bandImage S l q) := by
  rcases p with ⟨d,p⟩
  rcases q with ⟨e,q⟩
  change d < e ∨ ∃ same : d = e, OrbitLex d p (cast (congrArg OrbitCoords same.symm) q) at smaller
  rcases smaller with band | ⟨same,inside⟩
  · exact exact_OriginalTowerBandSeparation S l d e p q band
  · subst e
    exact (exact_OriginalAnchoredBand S l (bandStart S l d)
      (exact_OriginalBandStartRises S l d) d).2.2 p q inside

/-- The whole infinite sum, not just each separate finite-dimensional family,
lies strictly below the same genuine printed t_(l+2). -/
theorem exact_OriginalTowerVariableDimensionLexSum (S : Signature) (l : Nat) :
    (∀ p : BandCoords, NativeBelow (bandImage S l p) (closedTower S (l+2))) ∧
    (∀ p q : BandCoords, BandLex p q → NativeBelow (bandImage S l p) (bandImage S l q)) := by
  refine ⟨?_,exact_OriginalTowerBandLexPreservation S l⟩
  obtain ⟨mapping,seed,cone⟩ := exact_ActualOriginalOuterIndexCone S l
  intro p
  have admitted := transBase (exact_OriginalTowerBandEndpoints S l p.1 p.2).2
    (exact_OriginalBandStartAdmitted cone (p.1+1))
  exact transBase admitted (positiveRun cone.towerRun (by omega))

#print axioms exact_OriginalAnchoredBand
#print axioms exact_OriginalTowerBandEndpoints
#print axioms exact_OriginalTowerBandSeparation
#print axioms exact_OriginalTowerBandLexPreservation
#print axioms exact_OriginalTowerVariableDimensionLexSum

end LogicLineages.PersistentMarking.NativeTowerVariableDimensionBandsProof
