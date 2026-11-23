import LogicLineages.PersistentMarking.NativeTowerBoundedInnerOrbitBlocksProof

namespace LogicLineages.PersistentMarking.NativeTowerOuterIndexConeProof
open Spine NativeIteratorStrictTargets NativeClosedApplication NativeIndexedCarrierTargets NativeIndexedCarrierSubtype
open NativeOrdinalBasisTargets NativeOrdinalCapPathsTargets NativeOrdinalArithmeticTargets
open NativeTowerWitnessPrefixProof NativeTowerWitnessFamilyProof
open NativeTowerWitnessPrefixTargets NativeTowerBetaPathProof
open NativeTowerIndexedEntryTargets NativeTowerIndexedEntryProof
open NativeTowerInnerMapSubstitutionProof NativeTowerInnerMapHigherIteratorProof
open NativeIndexedCarrierFiniteOrbitProof NativeIndexedCarrierOrbitBlocksProof
open NativeTowerBoundedInnerOrbitBlocksProof

abbrev Base (S : Signature) := ClosedNativeTerm S indexType
abbrev Map (S : Signature) := ClosedNativeTerm S endo

def actualOuter (S : Signature) (mapping : Map S) (seed : Base S) : Base S :=
  indexedTerm .base mapping seed (closedOmega S)

def evaluatedInner (S : Signature) (l : Nat) (index : Base S) : Base S :=
  originalInnerOrbitBlock S l index 0

structure ActualIndexCone (S : Signature) (l : Nat) (mapping : Map S) (seed : Base S) : Prop where
  actualMap : mapping.val = innerMap l
  actualSeed : seed.val = successorSeed
  towerRun : StrictRun S (l+6) (closedTower S (l+2)) (actualOuter S mapping seed)
  omegaAdmitted : NativeBelow (closedOmega S) (actualOuter S mapping seed)

theorem transBase {S} {a b c : Base S}
    (ab : NativeBelow a b) (bc : NativeBelow b c) : NativeBelow a c :=
  StablePairProof.strictTransitive S c.val b.val a.val bc ab

theorem positiveRun {S} {n : Nat} {a b : Base S}
    (run : StrictRun S n a b) : n ≠ 0 → NativeBelow b a := by
  induction run with
  | nil => intro ne; exact False.elim (ne rfl)
  | @cons k _ _ _ _ edge tail ih =>
    intro _
    cases k with
    | zero => cases tail; exact edge
    | succ k => exact transBase (ih (Nat.succ_ne_zero k)) edge

theorem exact_ActualOriginalOuterIndexCone (S : Signature) (l : Nat) :
    ∃ (mapping : Map S) (seed : Base S), ActualIndexCone S l mapping seed := by
  obtain ⟨mapping,seed,out,realMap,realSeed,realOut,run⟩ := exact_NativeTowerIndexedEntry S l
  have outExact : out = actualOuter S mapping seed := by
    apply Subtype.ext
    change out.val = indexedW .base mapping.val seed.val omegaCarrier
    rw [realMap,realSeed]
    exact realOut
  rw [outExact] at run
  have omegaBelowT0 : NativeBelow (closedOmega S) (closedT0 S) :=
    exact_SameTypedNativeApplicationSelect (nativeNb S) (closedOmega S)
  have seedExact : seed = applyClosed (closedSuccessor S) (closedT0 S) := Subtype.ext realSeed
  have t0BelowSeed : NativeBelow (closedT0 S) seed := by
    rw [seedExact]
    exact exact_SameTypedNativeApplicationSelect (closedSuccessor S) (closedT0 S)
  have seedAdmitted : NativeBelow seed (actualOuter S mapping seed) :=
    exact_IndexedCarrierFiniteSeedOrbit .base mapping seed (closedOmega S) 0
  exact ⟨mapping,seed,⟨realMap,realSeed,run,transBase (transBase omegaBelowT0 t0BelowSeed) seedAdmitted⟩⟩

/-- Use the same fixed genuine outer carrier: evaluating the real inner map
at any index already in its lower cone stays in that very cone. -/
theorem exact_EvaluatedInnerStaysInActualCone {S l mapping seed}
    (cone : ActualIndexCone S l mapping seed) (j : Base S)
    (admitted : NativeBelow j (actualOuter S mapping seed)) :
    NativeBelow (evaluatedInner S l j) (actualOuter S mapping seed) := by
  have applied : NativeBelow (applyClosed mapping j) (actualOuter S mapping seed) :=
    exact_IndexedCarrierFiniteAbsorption .base mapping seed j (closedOmega S) admitted 1
  have evaluated : NativeBelow (evaluatedInner S l j) (applyClosed mapping j) :=
    positiveRun (exact_OriginalInnerMapHigherIteratorRun S l mapping j cone.actualMap) (by decide)
  exact transBase evaluated applied

/-- A genuinely smaller index bounds all its orbit copies by the *evaluated*
larger index, not just by the unevaluated printed top. -/
theorem exact_OriginalInnerOrbitIndexCut (S : Signature) (l : Nat)
    (i j : Base S) (earlier : NativeBelow i j) (m : Nat) :
    NativeBelow (originalInnerOrbitBlock S l i m) (evaluatedInner S l j) :=
  exact_OriginalPaidDrainStrict S l _ _
    (exact_IndexedCarrierFiniteEarlierOrbit (level l) (actualArg S l) (paidOperand S l) j i earlier m)

theorem exact_OriginalInnerOrbitCrossIndex (S : Signature) (l : Nat)
    (i j : Base S) (earlier : NativeBelow i j) (m n : Nat) :
    NativeBelow (originalInnerOrbitBlock S l i m) (originalInnerOrbitBlock S l j n) :=
  exact_OriginalPaidDrainStrict S l _ _
    (exact_IndexedOrbitBlockSeparation (level l) (actualArg S l) (paidOperand S l) i j earlier m n)

theorem exact_OriginalInnerOrbitSameIndex (S : Signature) (l : Nat)
    (i : Base S) {m n : Nat} (earlier : m < n) :
    NativeBelow (originalInnerOrbitBlock S l i m) (originalInnerOrbitBlock S l i n) :=
  exact_OriginalPaidDrainStrict S l _ _
    (exact_SameTypedNativeFiniteOrbitStrict (actualArg S l) (printedIndexedHead S l i) earlier)

#print axioms exact_ActualOriginalOuterIndexCone
#print axioms exact_EvaluatedInnerStaysInActualCone
#print axioms exact_OriginalInnerOrbitIndexCut
#print axioms exact_OriginalInnerOrbitCrossIndex
#print axioms exact_OriginalInnerOrbitSameIndex

end LogicLineages.PersistentMarking.NativeTowerOuterIndexConeProof
