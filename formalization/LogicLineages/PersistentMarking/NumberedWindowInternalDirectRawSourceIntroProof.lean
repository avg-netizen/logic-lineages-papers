module
public import LogicLineages.PersistentMarking.NumberedWindowInternalCertifiedUnionStepProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendListProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestPredecessorProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalDirectRawSourceIntroProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalApplicationValidityStackAppend (append)
open ID1Completion.InternalAcceptance (conjunction constantZero)
open ID1Completion.InternalAcceptanceBranchProof (successorBranchIntro)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionAccept)
open ID1Completion.InternalLessThan (constantOne)
open ID1Completion.InternalLessThanSupportProof (oneConstantValue)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue)
open ID1Completion.InternalEqualityTest (predecessor)
open ID1Completion.InternalEqualityTestPredecessorProof (predecessorSuccessor)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalDirectSourcePartitionRawTargets
open NumberedWindowInternalSparsePathEnvelopeTargets (unary suc z)
open NumberedWindowInternalSparseFieldParser (parser)

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

abbrev Report {n : Nat} (p : Program n) (out : OTerm α) (xs : Fin n → OTerm α) : Prop :=
  Nonempty (Derivation B Γ (programGraph p out xs))

theorem onParser (i : Fin 3) (xs : Fin 3 → OTerm α) (out : OTerm α)
    (held : Report (B := B) (Γ := Γ) parser (suc out) ![xs i]) :
    Report (B := B) (Γ := Γ) (parserAt i) (suc out) xs := by
  apply compositionValue parser ![.projection i] (suc out) xs ![xs i] held
  intro q
  obtain rfl := Fin.eq_zero q
  exact projectionValue i xs

theorem parsed (i : Fin 3) (xs : Fin 3 → OTerm α) (out : OTerm α)
    (held : Report (B := B) (Γ := Γ) parser (suc out) ![xs i]) :
    Report (B := B) (Γ := Γ) (parsedAt i) (suc z) xs :=
  successorBranchIntro (parserAt i) (constantZero 3) (constantOne 3)
    (suc z) out xs (onParser i xs out held) (oneConstantValue xs)

theorem payload (i : Fin 3) (xs : Fin 3 → OTerm α) (out : OTerm α)
    (held : Report (B := B) (Γ := Γ) parser (suc out) ![xs i]) :
    Report (B := B) (Γ := Γ) (payloadAt i) out xs := by
  apply compositionValue predecessor ![parserAt i] out xs ![suc out] (predecessorSuccessor out)
  intro q
  obtain rfl := Fin.eq_zero q
  exact onParser i xs out held

/-- Inverse constructor of the actual original three-parser check. All
parser guards and decoded parameters refer to the same input fields. -/
theorem exact_OriginalRawSourceFromDecoded (check : Program 3)
    (a b c da db dc : OTerm α) (pr : ParsedTriplet B Γ a b c da db dc)
    (accepted : Report (B := B) (Γ := Γ) check (suc z) (sourceTape da db dc)) :
    Report (B := B) (Γ := Γ) (rawSourceCheck check) (suc z) (sourceTape a b c) := by
  let scratch := sourceTape da db dc
  let raw := sourceTape a b c
  have decoded : Report (B := B) (Γ := Γ) (decodedCall check) (suc z) raw := by
    apply compositionValue check ![payloadAt 0,payloadAt 1,payloadAt 2]
      (suc z) raw scratch accepted
    intro i
    exact Fin.cases (payload 0 raw da pr.source)
      (Fin.cases (payload 1 raw db pr.kept)
        (Fin.cases (payload 2 raw dc pr.removed) (fun j => Fin.elim0 j))) i
  have ready := conjunctionAccept (parsedAt 0) (conjunction (parsedAt 1) (parsedAt 2)) raw
    (parsed 0 raw da pr.source)
    (conjunctionAccept (parsedAt 1) (parsedAt 2) raw
      (parsed 1 raw db pr.kept) (parsed 2 raw dc pr.removed))
  exact conjunctionAccept parsedAll (decodedCall check) raw ready decoded

#print axioms exact_OriginalRawSourceFromDecoded
end LogicLineages.PersistentMarking.NumberedWindowInternalDirectRawSourceIntroProof
