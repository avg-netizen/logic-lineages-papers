module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationTargets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationSignatureSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedLeastCodeRepresentative
open NumberedHereditaryView OriginalRootObservation

theorem typedCalibration (R : Program 2) {n : Nat} {arity : Fin n → Nat}
    (symbols : List (Fin n)) (S : List Ty) (c : Nat)
    (hR : ∀ (Gamma : List Ty) (q : Packed (Fin n) arity Gamma),
      evaluate R (List.Vector.ofFn ![packedNumber q,Nat.pair c (typesNumber Gamma)]) = representativeCode symbols S q)
    {Gamma : List Ty} (q : Packed (Fin n) arity Gamma) :
    typedValue R c q = typedNumber (typedCode symbols S q) := by
  unfold typedValue typedNumber typedCode
  rw [hR Gamma q]

theorem argumentCalibration (R : Program 2) {n : Nat} {arity : Fin n → Nat}
    (symbols : List (Fin n)) (S : List Ty) (c : Nat)
    (hR : ∀ (Gamma : List Ty) (q : Packed (Fin n) arity Gamma),
      evaluate R (List.Vector.ofFn ![packedNumber q,Nat.pair c (typesNumber Gamma)]) = representativeCode symbols S q)
    {Gamma types : List Ty} (args : AuxArguments (Fin n) arity Gamma types) :
    argumentValues R c args = (SourceZeroNumberedComputability.argumentCodes symbols S args).map typedNumber := by
  unfold argumentValues SourceZeroNumberedComputability.argumentCodes
  rw [List.map_map]
  apply List.map_congr_left
  intro q hq
  exact typedCalibration R symbols S c hR q

/-- Sorting numeric typed observations implements the literal multiset
encoding; equal elements and their multiplicities are retained. -/
theorem sortedEncoding (xs : List (Ty × Nat)) :
    NumberedMultisetNumeric.numbersNumber ((xs.map typedNumber).insertionSort (· ≤ ·)) =
      multisetNumber (xs : Multiset (Ty × Nat)) := by
  have hm : (xs : Multiset (Ty × Nat)).map typedNumber = (xs.map typedNumber : Multiset Nat) := rfl
  rw [multisetNumber,hm,Multiset.coe_sort,List.mergeSort_eq_insertionSort]

theorem nativeSignature (R : Program 2) {n : Nat} {arity : Fin n → Nat}
    (symbols : List (Fin n)) (S : List Ty) (c : Nat)
    (hR : ∀ (Gamma : List Ty) (q : Packed (Fin n) arity Gamma),
      evaluate R (List.Vector.ofFn ![packedNumber q,Nat.pair c (typesNumber Gamma)]) = representativeCode symbols S q)
    {Gamma : List Ty} (q : Packed (Fin n) arity Gamma) :
    nativeValue R c q = signatureNumber (rootSignature symbols S q) := by
  rcases q with ⟨tau,q⟩
  cases q <;> simp only [nativeValue,rootSignature,signatureNumber,
    typedCalibration R symbols S c hR,argumentCalibration R symbols S c hR,sortedEncoding]
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationSignatureSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationSignatureSupportProof
