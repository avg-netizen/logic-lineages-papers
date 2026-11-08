module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationValidityStackAppend
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem actualOriginalRawListAppendZero :
    InternalApplicationValidityStackAppendTargets.ActualOriginalRawListAppendZero :=
  InternalApplicationValidityStackAppendListProof.actualOriginalRawListAppendZero

theorem actualOriginalRawListAppendCons :
    InternalApplicationValidityStackAppendTargets.ActualOriginalRawListAppendCons :=
  InternalApplicationValidityStackAppendListProof.actualOriginalRawListAppendCons

theorem actualOriginalSuccessfulWorkAppend :
    InternalApplicationValidityStackAppendTargets.ActualOriginalSuccessfulWorkAppend :=
  InternalApplicationValidityStackAppendInductionProof.actualOriginalSuccessfulWorkAppend

/-- Contextual consumer of the same frozen internal sequential-success law. -/
theorem successfulAppend {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}
    (node leaf : Program 1) (first second frontWork suffix joined : OrdinaryArithmetic.Term α)
    (ha : Nonempty (Derivation body Gamma (graph2 append joined frontWork suffix)))
    (hf : Nonempty (Derivation body Gamma (successfulWork node leaf first frontWork)))
    (hs : Nonempty (Derivation body Gamma (successfulWork node leaf second suffix))) :
    Nonempty (Derivation body Gamma
      (successfulWork node leaf (OrdinaryArithmetic.addTerm first second) joined)) :=
  InternalApplicationValidityStackAppendInductionCoreProof.rowApply node leaf first second frontWork suffix joined
    (InternalApplicationValidityStackAppendInductionProof.allRows node leaf first) ha hf hs

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendProof
