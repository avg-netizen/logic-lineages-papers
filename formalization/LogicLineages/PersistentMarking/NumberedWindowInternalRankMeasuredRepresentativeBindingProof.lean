module
public import LogicLineages.PersistentMarking.NumberedWindowInternalRankMeasuredRoundApplicationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedRoundApplicationSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDecodeSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalRankMeasuredRepresentativeBindingProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open ID1Completion.InternalControlGraphSupportProof (valueUnique)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open ID1Completion.InternalTagArithmeticSupportProof (cancelSuc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparseScalarEdge (edge4)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary rawCons suc)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (rawConsRename)
open NumberedWindowInternalSparseDecodeSyntaxProof (unaryInputsRename)
open NumberedWindowInternalCoverCombinedRestrictedRoundApplicationSyntaxProof (appAuxRename)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparsePackedLeast (packedLeastProgram)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)
open NumberedWindowInternalSparsePackedLeastOpenSyntaxProof (leastRename)
open NumberedWindowInternalMeasuredPairedGuardedThinNumericProof (measuredFactoredExchange)
open NumberedWindowInternalMeasuredUnrestrictedWindowDefinitions (window)
open NumberedWindowInternalFactoredCoverTargets (factoredCover)
open NumberedWindowInternalAuxMeasureMemoTargets (selectedMeasure)
open NumberedWindowInternalAuxMeasureStepTargets (measureUpdate)
open NumberedWindowInternalMeasuredUnrestrictedRoundApplicationProof (ParentWindowsAt)
open NumberedWindowInternalRankMeasuredRoundApplicationProof (exact_OpenRankMeasuredRepresentative)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalRankMeasuredExchange (rankedExchange)
open NumberedWindowInternalMeasuredExchangeThinDefinitions (measuredExchange)
open NumberedWindowInternalAuxExchangeMemoStepTargets (step)
open NumberedWindowInternalAuxExchangeMemoTargets (selected)
open NumberedWindowInternalTransparentAuxRankTargets (auxRank)

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem windowsMove {β : Type} (E : Program 4) (W : Program 3)
    (ctx dom cod arg : OTerm α) (j : α → β) (Δ : List (Formula β))
    (keep : ∀ p ∈ Γ, p.relabel j ∈ Δ)
    (held : ParentWindowsAt E W B Γ ctx dom cod arg) :
    ParentWindowsAt E W B Δ (ctx.relabel j) (dom.relabel j) (cod.relabel j) (arg.relabel j) := by
  intro γ k Θ f g retained edge
  have both (p : Formula α) (hp : p ∈ Γ) : p.relabel (k ∘ j) ∈ Θ := by
    rw [← formulaRelabelComposition j k p]
    exact retained _ (keep p hp)
  have facts := held γ (k ∘ j) Θ f g both (by simpa only [Term.relabel_relabel] using edge)
  simpa only [Term.relabel_relabel] using facts

/-- The actual representative application law, with the genuine function
rank selected by the open calculus instead of held by the caller. -/
theorem exact_OpenRankMeasuredRepresentativeBinding
    (s : Settings) (base : Program 2) (V baseM g : Program 1) (P : Program 2) (G baseW : Program 3)
    (ctx dom cod f q arg m : OTerm α) :
    let M := selectedMeasure (measureUpdate baseM P)
    let C := factoredCover V M G
    let W := window C s baseW V
    let R := auxRank g
    let D := measuredExchange M (selected (step base V))
    let X := rankedExchange C s R D
    ParentWindowsAt (edge4 X W) W B Γ ctx dom cod arg →
    Nonempty (Derivation B Γ (leastGraph C X W s ctx (rawCons dom cod) f q)) →
    Nonempty (Derivation B Γ (leastGraph C X W s ctx cod (auxiliaryTerm dom cod f arg) m)) →
    Nonempty (Derivation B Γ (leastGraph C X W s ctx cod (auxiliaryTerm dom cod q arg) m)) := by
  intro M C W R D X held klass app
  apply programCases R ![f] _
  intro β j Δ μ keep value
  rw [leastRename,appAuxRename]
  rw [unaryInputsRename] at value
  have cl := renameInto klass j Δ keep
  have ap := renameInto app j Δ keep
  rw [leastRename,rawConsRename] at cl
  rw [leastRename,appAuxRename] at ap
  have windows := windowsMove (edge4 X W) W ctx dom cod arg j Δ keep held
  obtain ⟨moved⟩ := exact_OpenRankMeasuredRepresentative s base V baseM g P G baseW
    B β Δ (ctx.relabel j) (dom.relabel j) (cod.relabel j) (f.relabel j) (q.relabel j)
    (arg.relabel j) μ (m.relabel j) windows value cl ap
  exact ⟨Derivation.conjunctionRight moved⟩

#print axioms exact_OpenRankMeasuredRepresentativeBinding
end LogicLineages.PersistentMarking.NumberedWindowInternalRankMeasuredRepresentativeBindingProof
