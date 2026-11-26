module
public import LogicLineages.PersistentMarking.NumberedWindowInternalCertifiedUnionStepProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendListProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestPredecessorProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalConsUnionReportBuildProof
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
open NumberedWindowInternalCertifiedUnionStepProof (unionGraph)

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

abbrev Report {n : Nat} (p : Program n) (out : OTerm α) (xs : Fin n → OTerm α) : Prop :=
  Nonempty (Derivation B Γ (programGraph p out xs))

private theorem onParser (i : Fin 3) (xs : Fin 3 → OTerm α) (out : OTerm α)
    (held : Report (B := B) (Γ := Γ) parser (suc out) ![xs i]) :
    Report (B := B) (Γ := Γ) (parserAt i) (suc out) xs := by
  apply compositionValue parser ![.projection i] (suc out) xs ![xs i] held
  intro q
  obtain rfl := Fin.eq_zero q
  exact projectionValue i xs

private theorem parsed (i : Fin 3) (xs : Fin 3 → OTerm α) (out : OTerm α)
    (held : Report (B := B) (Γ := Γ) parser (suc out) ![xs i]) :
    Report (B := B) (Γ := Γ) (parsedAt i) (suc z) xs :=
  successorBranchIntro (parserAt i) (constantZero 3) (constantOne 3)
    (suc z) out xs (onParser i xs out held) (oneConstantValue xs)

private theorem payload (i : Fin 3) (xs : Fin 3 → OTerm α) (out : OTerm α)
    (held : Report (B := B) (Γ := Γ) parser (suc out) ![xs i]) :
    Report (B := B) (Γ := Γ) (payloadAt i) out xs := by
  apply compositionValue predecessor ![parserAt i] out xs ![suc out] (predecessorSuccessor out)
  intro q
  obtain rfl := Fin.eq_zero q
  exact onParser i xs out held

/-- Assemble the original raw partition program with literal parser reports,
literal scratch append, and the actual acceptance graph of the observer. -/
theorem unionReportOfGraphs (count : Program 2) (a b u sa sb su joined : OTerm α)
    (reports : ParsedTriplet B Γ u a b su sa sb)
    (written : Report (B := B) (Γ := Γ) append joined ![sa,sb])
    (observed : Report (B := B) (Γ := Γ) count (suc z) ![su,joined]) :
    Nonempty (Derivation B Γ (unionGraph count a b u)) := by
  let scratch := sourceTape su sa sb
  let raw := sourceTape u a b
  have joinedAt : Report (B := B) (Γ := Γ) appendKeptRemoved joined scratch := by
    apply compositionValue append ![.projection 1,.projection 2] joined scratch ![sa,sb] written
    intro i
    exact Fin.cases (projectionValue 1 scratch)
      (Fin.cases (projectionValue 2 scratch) (fun j => Fin.elim0 j)) i
  have accepted : Report (B := B) (Γ := Γ) (observePartition count) (suc z) scratch := by
    apply compositionValue count ![.projection 0,appendKeptRemoved] (suc z) scratch ![su,joined] observed
    intro i
    exact Fin.cases (projectionValue 0 scratch) (Fin.cases joinedAt (fun j => Fin.elim0 j)) i
  have decoded : Report (B := B) (Γ := Γ) (decodedCall (observePartition count)) (suc z) raw := by
    apply compositionValue (observePartition count) ![payloadAt 0,payloadAt 1,payloadAt 2]
      (suc z) raw scratch accepted
    intro i
    exact Fin.cases (payload 0 raw su reports.source)
      (Fin.cases (payload 1 raw sa reports.kept)
        (Fin.cases (payload 2 raw sb reports.removed) (fun j => Fin.elim0 j))) i
  have flags := conjunctionAccept (parsedAt 0) (conjunction (parsedAt 1) (parsedAt 2)) raw
    (parsed 0 raw su reports.source)
    (conjunctionAccept (parsedAt 1) (parsedAt 2) raw
      (parsed 1 raw sa reports.kept) (parsed 2 raw sb reports.removed))
  exact conjunctionAccept parsedAll (decodedCall (observePartition count)) raw flags decoded

#print axioms unionReportOfGraphs

end LogicLineages.PersistentMarking.NumberedWindowInternalConsUnionReportBuildProof
