module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsEvaluationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortNativeProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open OriginalNumericListSort NumberedMultisetNumeric NumberedMultisetNumericSupportProof
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsEvaluationProof
open InternalAcceptanceCalibrationProof InternalRawListRecursionEvaluationProof
open InternalEqualityTestEvaluationProof (vectorOne vectorTwo)
attribute [local irreducible] InternalPairing.pairing InternalUnpair.left InternalUnpair.right InternalListCodec.consCode

theorem baseEvaluation (x : Nat) :
    evaluate insertBase (x ::ᵥ nil) = Nat.pair 0 (numbersNumber [x]) := by
  change evaluate (pairOf InternalRawListRecursion.zero (consOf (.projection 0) InternalRawListRecursion.zero)) (x ::ᵥ nil) = _
  rw [pairOfEvaluation,consOfEvaluation]
  rfl

theorem originalEvaluation (head old result x : Nat) :
    evaluate originalCons (head ::ᵥ Nat.pair old result ::ᵥ x ::ᵥ nil) = 1 + Nat.pair head old := by
  change evaluate (consOf (.projection 0) (leftOf (.projection 1))) _ = _
  rw [consOfEvaluation,leftOfEvaluation]
  simp [evaluate]

theorem beforeEvaluation (head old result x : Nat) :
    evaluate beforeCons (head ::ᵥ Nat.pair old result ::ᵥ x ::ᵥ nil) = 1 + Nat.pair x (1 + Nat.pair head old) := by
  change evaluate (consOf (.projection 2) originalCons) _ = _
  rw [consOfEvaluation,originalEvaluation]
  rfl

theorem afterEvaluation (head old result x : Nat) :
    evaluate afterCons (head ::ᵥ Nat.pair old result ::ᵥ x ::ᵥ nil) = 1 + Nat.pair head result := by
  change evaluate (consOf (.projection 0) (rightOf (.projection 1))) _ = _
  rw [consOfEvaluation,rightOfEvaluation]
  simp [evaluate]

theorem stepEvaluation (head old result x : Nat) :
    evaluate insertStep (head ::ᵥ Nat.pair old result ::ᵥ x ::ᵥ nil) =
      Nat.pair (1 + Nat.pair head old)
        (if x ≤ head then 1 + Nat.pair x (1 + Nat.pair head old) else 1 + Nat.pair head result) := by
  change evaluate (pairOf originalCons (InternalAcceptance.branch
    (.composition InternalLessThan.ltTest ![.projection 0,.projection 2]) beforeCons afterCons)) _ = _
  rw [pairOfEvaluation,originalEvaluation,evalBranch,beforeEvaluation,afterEvaluation]
  have hc : evaluate (.composition InternalLessThan.ltTest ![.projection 0,.projection 2])
      (head ::ᵥ Nat.pair old result ::ᵥ x ::ᵥ nil) = if head < x then 1 else 0 := by
    change evaluate InternalLessThan.ltTest (ofFn fun k : Fin 2 => evaluate
      ((![.projection 0,.projection 2] : Fin 2 → Program 3) k) (head ::ᵥ Nat.pair old result ::ᵥ x ::ᵥ nil)) = _
    rw [vectorTwo]
    exact InternalLessThanEvaluationProof.exactLessThanEvaluation head x
  rw [hc]
  by_cases h : x ≤ head
  · simp [h,Nat.not_lt.mpr h]
  · simp [h,Nat.lt_of_not_ge h]

theorem stateFold (xs : List Nat) (x : Nat) :
    xs.foldr (fun head state => evaluate insertStep (head ::ᵥ state ::ᵥ x ::ᵥ nil))
      (evaluate insertBase (x ::ᵥ nil)) = Nat.pair (numbersNumber xs)
        (numbersNumber (xs.orderedInsert (· ≤ ·) x)) := by
  induction xs with
  | nil => simpa only [List.foldr_nil,List.orderedInsert_nil,numbersNumber] using baseEvaluation x
  | cons head tail ih =>
    rw [List.foldr_cons,ih,stepEvaluation]
    simp only [List.orderedInsert_cons,numbersNumber]
    split <;> rfl

theorem insertEvaluation (xs : List Nat) (x : Nat) :
    evaluate insert (numbersNumber xs ::ᵥ x ::ᵥ nil) = numbersNumber (xs.orderedInsert (· ≤ ·) x) := by
  change evaluate (rightOf insertState) _ = _
  rw [rightOfEvaluation]
  have h : evaluate insertState (numbersNumber xs ::ᵥ x ::ᵥ nil) =
      Nat.pair (numbersNumber xs) (numbersNumber (xs.orderedInsert (· ≤ ·) x)) := by
    rw [insertState,actualRawListRecursionEvaluation,numbersRoundTrip]
    exact stateFold xs x
  rw [h]
  simp

theorem sortStepEvaluation (head : Nat) (tail : List Nat) :
    evaluate sortStep (head ::ᵥ numbersNumber tail ::ᵥ nil) = numbersNumber (tail.orderedInsert (· ≤ ·) head) := by
  change evaluate insert (ofFn fun k : Fin 2 => evaluate
    ((![.projection 1,.projection 0] : Fin 2 → Program 2) k) (head ::ᵥ numbersNumber tail ::ᵥ nil)) = _
  rw [vectorTwo]
  exact insertEvaluation tail head

theorem nativeCalibration : OriginalNumericListSortTargets.NativeCalibration := by
  intro xs
  rw [sort,actualRawListRecursionEvaluation,numbersRoundTrip]
  change xs.foldr (fun head state => evaluate sortStep (head ::ᵥ state ::ᵥ nil)) 0 = _
  induction xs with
  | nil => rfl
  | cons head tail ih =>
    rw [List.foldr_cons,ih,sortStepEvaluation,List.insertionSort_cons]

theorem numbersInjective : Function.Injective numbersNumber := by
  intro xs ys he
  have h := numbersRoundTrip xs
  rw [he,numbersRoundTrip] at h
  exact Option.some.inj h.symm

theorem nativePermutation : OriginalNumericListSortTargets.NativePermutation := by
  intro xs ys
  rw [nativeCalibration,nativeCalibration]
  constructor
  · intro he
    have hs := numbersInjective he
    have hx := List.perm_insertionSort (· ≤ ·) xs
    rw [hs] at hx
    exact hx.symm.trans (List.perm_insertionSort (· ≤ ·) ys)
  · intro hp
    have hs := ((List.perm_insertionSort (· ≤ ·) xs).trans
      (hp.trans (List.perm_insertionSort (· ≤ ·) ys).symm)).eq_of_pairwise'
        (List.pairwise_insertionSort (· ≤ ·) xs) (List.pairwise_insertionSort (· ≤ ·) ys)
    exact congrArg numbersNumber hs
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortNativeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortNativeProof
