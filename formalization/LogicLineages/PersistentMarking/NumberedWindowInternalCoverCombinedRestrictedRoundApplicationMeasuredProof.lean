module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedRoundApplicationCombinedTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredAuxExchangeCompareProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScalarEdgeOpenChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedRoundApplicationMeasuredProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (outputTransport valueUnique)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionRecover)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparseScalarEdge (edge4 exchangeTape)
open NumberedWindowInternalSparseDirectedSeen (acceptEdge)
open NumberedWindowInternalSparseCoverGuardedExchangeTargets (guardedExchange compareOptions)
open NumberedWindowInternalCoverCombinedRestrictedPairedAuxTargets (thinPairedExchange thinSwapExchange)
open NumberedWindowInternalMeasuredAuxExchangeTargets (measuredExchange compareMeasurements)
open NumberedWindowInternalMeasuredAuxExchangeCompareProof (compareCases)
open NumberedWindowInternalSparseScalarEdgeOpenChecks (exact_OpenPackedScalarEdge)
open NumberedWindowInternalCoverCombinedRestrictedRoundApplicationCombinedTargets

attribute [local irreducible] programGraph

theorem exact_MeasuredExchangePreservesMeasure : ExactMeasuredExchangePreservesMeasure := by
  intro C s M D W body α Γ fctx fty μ w k
  let X := guardedExchange C s (thinPairedExchange (measuredExchange M D))
  let A := acceptEdge (edge4 X W) fctx fty w k ⊓ unary M μ w
  let Δ := A :: Γ
  have h : Derivation body Δ A := Derivation.hypothesis List.mem_cons_self
  obtain ⟨lawX⟩ := exact_OpenPackedScalarEdge X W body α Δ fctx fty w k
  have calls := Derivation.implicationElimination (Derivation.conjunctionLeft lawX) (Derivation.conjunctionLeft h)
  obtain ⟨g⟩ := conjunctionRecover (thinPairedExchange (measuredExchange M D)) (compareOptions C s)
    (exchangeTape w k) ⟨Derivation.conjunctionLeft calls⟩
  obtain ⟨pp⟩ := conjunctionRecover (measuredExchange M D) (thinSwapExchange (measuredExchange M D))
    (exchangeTape w k) ⟨Derivation.conjunctionLeft g⟩
  obtain ⟨mm⟩ := conjunctionRecover D (compareMeasurements M) (exchangeTape w k) ⟨Derivation.conjunctionLeft pp⟩
  have result : Nonempty (Derivation body Δ (unary M μ k)) := by
    apply compareCases M w k (unary M μ k) ⟨Derivation.conjunctionRight mm⟩
    intro β j Θ n keep nw nk
    rw [unaryRename]
    have mu := renameInto ⟨Derivation.conjunctionRight h⟩ j Θ keep
    rw [unaryRename] at mu
    have e := valueUnique M n (μ.relabel j) ![w.relabel j] nw mu
    exact outputTransport M n (μ.relabel j) ![k.relabel j] e nk
  obtain ⟨r⟩ := result
  exact ⟨Derivation.implicationIntroduction r⟩

#print axioms exact_MeasuredExchangePreservesMeasure
end LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedRoundApplicationMeasuredProof
