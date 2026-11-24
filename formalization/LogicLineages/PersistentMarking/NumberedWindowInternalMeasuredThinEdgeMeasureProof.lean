module

public import LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredPairedGuardedThinNumericProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedSeenDefinitions
import LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredExchangeThinOpenCompareProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScalarEdgeOpenChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredThinEdgeMeasureProof
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
open NumberedWindowInternalMeasuredPairedGuardedThinNumericProof (pairedExchange swapExchange)
open NumberedWindowInternalMeasuredExchangeThinDefinitions (measuredExchange compareMeasurements)
open NumberedWindowInternalMeasuredExchangeThinOpenCompareProof (compareCases)
open NumberedWindowInternalSparseScalarEdgeOpenChecks (exact_OpenPackedScalarEdge)
open NumberedWindowScalarAlgorithm (Settings)

attribute [local irreducible] programGraph

theorem exact_OpenThinMeasuredEdgePreservesMeasure (C : Program 3) (s : Settings)
    (M : Program 1) (D : Program 2) (W : Program 3)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (fctx fty μ w k : OTerm α) :
    let X := guardedExchange C s (pairedExchange (measuredExchange M D))
    Nonempty (Derivation body Γ
      ((acceptEdge (edge4 X W) fctx fty w k ⊓ unary M μ w).imp (unary M μ k))) := by
  let X := guardedExchange C s (pairedExchange (measuredExchange M D))
  let A := acceptEdge (edge4 X W) fctx fty w k ⊓ unary M μ w
  let Δ := A :: Γ
  have h : Derivation body Δ A := Derivation.hypothesis List.mem_cons_self
  obtain ⟨lawX⟩ := exact_OpenPackedScalarEdge X W body α Δ fctx fty w k
  have calls := Derivation.implicationElimination (Derivation.conjunctionLeft lawX) (Derivation.conjunctionLeft h)
  obtain ⟨g⟩ := conjunctionRecover (pairedExchange (measuredExchange M D)) (compareOptions C s)
    (exchangeTape w k) ⟨Derivation.conjunctionLeft calls⟩
  obtain ⟨pp⟩ := conjunctionRecover (measuredExchange M D) (swapExchange (measuredExchange M D))
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

#print axioms exact_OpenThinMeasuredEdgePreservesMeasure
end LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredThinEdgeMeasureProof
