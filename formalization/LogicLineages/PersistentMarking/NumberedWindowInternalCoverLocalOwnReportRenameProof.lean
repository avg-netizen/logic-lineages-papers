module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLocalOwnContinuationTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverLocalOwnReportRenameProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (zRelabel sucRelabel)
open ID1Completion.GuardedSourceSyntaxProof (numeralRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalFactoredAuxOwnCoverTargets (typesTerm)
open NumberedWindowInternalCoverLocalOwnContinuationTargets

variable {body : Positive (Fin 1)} {α β : Type} {Γ : List (Formula α)} {Δ : List (Formula β)}

theorem moveParent (V : Program 1) (R : Program 4) (s : Settings)
    (j : α → β) (keep : ∀ f ∈ Γ, f.relabel j ∈ Δ) {key p vertices : OTerm α}
    (parent : ActualOwnParent V R s body Γ key p vertices) :
    ActualOwnParent V R s body Δ (key.relabel j) (p.relabel j) (vertices.relabel j) := by
  have valid := renameInto parent.valid j Δ keep
  have measured := renameInto parent.measured j Δ keep
  have held := renameInto parent.held j Δ keep
  simp only [unaryRename,sucRelabel,zRelabel] at valid
  rw [unaryRename] at measured held
  exact ⟨valid,measured,held⟩

theorem moveTypeMember (s : Settings) (j : α → β) (keep : ∀ f ∈ Γ, f.relabel j ∈ Δ)
    {ty : OTerm α} (member : Nonempty (Derivation body Γ (memberGraph (typesTerm s α) ty))) :
    Nonempty (Derivation body Δ (memberGraph (typesTerm s β) (ty.relabel j))) := by
  have actual := renameInto member j Δ keep
  simpa only [graphRename,typesTerm,numeralRename] using actual

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverLocalOwnReportRenameProof
