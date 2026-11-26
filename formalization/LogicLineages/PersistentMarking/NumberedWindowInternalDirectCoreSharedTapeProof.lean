module
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectCoreSharedTapeTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectCoreEnvelopeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSharedTapeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectWitnessEnvelopeOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSourcePartitionRawGraphProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphStepSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalDirectCoreSharedTape
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalDirectWitnessEnvelopeTargets (reports)
open NumberedWindowInternalDirectWitnessEnvelope (exactOpenTriple)
open NumberedWindowInternalDirectSourcePartitionRawGraphProof (keepThrough renameUnit)
open NumberedWindowInternalDirectBoundaryGuardsTargets (boundaryRaw)
open NumberedWindowInternalDirectCoreEnvelopeProof (exact_OpenDCore)
open NumberedWindowInternalDirectSharedTape (exactOpenSharedTape)
open NumberedWindowInternalDirectCoreSharedTapeTargets
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)

attribute [local irreducible] programGraph

private theorem renameEnvelope {B : Positive (Fin 1)} {α β : Type}
    {Γ : List (Formula α)} {Δ : List (Formula β)}
    (w k d a : OTerm α) (h : Nonempty (Derivation B Γ (reports 5 w k d a)))
    (j : α → β) (keep : ∀ f ∈ Γ, f.relabel j ∈ Δ) :
    Nonempty (Derivation B Δ (reports 5 (w.relabel j) (k.relabel j) (d.relabel j) (a.relabel j))) := by
  simpa only [reports,conjunctionRename,unaryRename,sucRelabel,zRelabel] using renameInto h j Δ keep

theorem exactOpenDCoreSharedTape : ExactOpenDCoreSharedTape := by
  intro scalar positive count B α Γ src w dst goal held next
  apply exact_OpenDCore scalar positive count B α Γ src w dst goal held
  intro β j Δ kept removed inserted keep packed _ cut
  apply exactOpenSharedTape count count positive B β Δ (src.relabel j) (dst.relabel j)
    kept removed inserted (goal.relabel j) cut.sourceObserver cut.targetObserver cut.insertionScan
  intro γ l Ω s t k d a p sk tp retain shared
  let ρ := l ∘ j
  have envelope : Nonempty (Derivation B Ω
      (reports 5 (w.relabel ρ) (kept.relabel l) (removed.relabel l) (inserted.relabel l))) := by
    simpa only [ρ,Term.relabel_relabel] using
      renameEnvelope (w.relabel j) kept removed inserted packed l retain
  have boundary := renameUnit (boundaryRaw scalar) (src.relabel j) (dst.relabel j) removed
    cut.scalarBoundary l Ω retain
  obtain ⟨facts⟩ := envelope
  obtain ⟨bridge⟩ := exactOpenTriple B γ Ω 5 (w.relabel ρ)
    (kept.relabel l) (removed.relabel l) (inserted.relabel l)
  have literal := Derivation.implicationElimination (Derivation.conjunctionRight bridge) facts
  rw [formulaRelabelComposition]
  apply next γ ρ Ω (kept.relabel l) (removed.relabel l) (inserted.relabel l) s t k d a p sk tp
    (keepThrough j l keep retain) ⟨facts⟩ ⟨literal⟩
  · simpa only [ρ,Term.relabel_relabel] using boundary
  · simpa only [ρ,Term.relabel_relabel] using shared

end LogicLineages.PersistentMarking.NumberedWindowInternalDirectCoreSharedTape
