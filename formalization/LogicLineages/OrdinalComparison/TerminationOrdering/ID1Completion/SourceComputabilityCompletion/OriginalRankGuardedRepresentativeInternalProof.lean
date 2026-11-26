module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRankGuardedRepresentativeGuardProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRankGuardedRepresentativeInternalProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open OriginalRankGuardedRepresentative
open InternalApplicationCertificateConstructors (graph1 graph2)
open InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Both actual graph premises pay the initial guard. The proof uses only
internal totality, graph functionality and the original raw-rank comparison;
no native calibration or final-fold assertion is needed. -/
theorem actualOriginalRankGuardedRepresentativeInternalRank :
    OriginalRankGuardedRepresentativeTargets.ActualOriginalRankGuardedRepresentativeInternalRank := by
  intro p H G W body α Delta out input parameter rank
  let q := transparentInputs H G W p
  let P := graph2 (BottomRepresentative.windowAt q.window)
      InternalOriginalStepGuard.one input parameter ⊓
    (graph2 q.base.oldSource InternalOriginalStepGuard.one input parameter ⊓
      graph2 q.base.oldRepresentative out input parameter)
  have hh : Derivation body (P :: Delta) P :=
    Derivation.hypothesis List.mem_cons_self
  have hw : Nonempty (Derivation body (P :: Delta)
      (graph2 (BottomRepresentative.windowAt q.window)
        InternalOriginalStepGuard.one input parameter)) :=
    ⟨Derivation.conjunctionLeft hh⟩
  have hs : Nonempty (Derivation body (P :: Delta)
      (graph2 q.base.oldSource InternalOriginalStepGuard.one input parameter)) :=
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight hh)⟩
  have hr : Nonempty (Derivation body (P :: Delta)
      (graph2 q.base.oldRepresentative out input parameter)) :=
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight hh)⟩
  have ha := InternalAcceptanceConjunctionProof.conjunctionAccept
    (BottomRepresentative.windowAt q.window) q.base.oldSource
    (Fin.cons input (Fin.cons parameter Fin.elim0)) hw hs
  change Nonempty (Derivation body (P :: Delta)
    (graph2 (representative q.base.oldSource p.base.oldRepresentative q.window)
      out input parameter)) at hr
  obtain ⟨h⟩ := OriginalRankGuardedRepresentativeGuardProof.preservation
    q.base.oldSource p.base.oldRepresentative q.window out input parameter rank ha hr
  exact ⟨Derivation.implicationIntroduction h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRankGuardedRepresentativeInternalProof
