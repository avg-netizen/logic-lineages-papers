module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverRefinedInductionDispatchTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverOwnEarlierSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLocalOwnReportRenameProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldCellSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathSuccessfulAdvanceGraphSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceIntroductionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionLawsProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverRefinedInductionDispatchTransportProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn emb bindTerm bindEmbedding liftBind varBind z suc zSubst sucSubst)
open ID1Completion.InternalStrongInduction (below)
open ID1Completion.InternalStrongInductionSyntaxProof (belowSubst belowRename)
open ID1Completion.InternalSourceIntroductionSyntaxProof (formulaRelabelAsSubst termRelabelAsSubst)
open ID1Completion.InternalAdditionLawsProof (impSubst)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (Reports)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparsePassWindowSyntaxProof (windowSubst memberSubst windowRename moveGuard)
open NumberedWindowInternalSparsePathSuccessfulAdvanceGraphSyntaxProof (unarySubst)
open NumberedWindowInternalSparseFieldCellSyntaxProof (moveUnary)
open NumberedWindowInternalSparseCoverScratch (scratchVertices)
open NumberedWindowInternalAuxMeasureMemoTargets (selectedMeasure)
open NumberedWindowInternalCoverLocalOwnReportRenameProof (moveParent)
open NumberedWindowInternalCoverOwnEarlierTargets
open NumberedWindowInternalCoverOwnEarlierSyntaxProof (ownAllSubst)
open NumberedWindowInternalCoverRefinedInductionDispatchTargets

variable {body : Positive (Fin 1)} {α β : Type} {Γ : List (Formula α)} {Δ : List (Formula β)}

private theorem ownAtSubst (V : Program 1) (W C : Program 3) (s : Settings) (q : OTerm α) (ts : α → OTerm β) :
    (ownAt V W C s q).subst (fun a => emb (ts a)) = ownAt V W C s (q.subst ts) := by
  simp only [ownAt,impSubst,unarySubst,ownAllSubst,sucSubst,zSubst]

private theorem ownAtRename (V : Program 1) (W C : Program 3) (s : Settings) (q : OTerm α) (j : α → β) :
    (ownAt V W C s q).relabel j = ownAt V W C s (q.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (ownAt V W C s q).subst (fun a => emb (.var (j a))) = _
  rw [ownAtSubst,← termRelabelAsSubst]

theorem ownBelowRename (V : Program 1) (W C : Program 3) (s : Settings) (q : OTerm α) (j : α → β) :
    (ownBelow V W C s q).relabel j = ownBelow V W C s (q.relabel j) := by
  rw [belowRename]
  unfold ownMotive
  rw [ownAtRename] <;> rfl

private def moveBelow (V : Program 1) (W C : Program 3) (s : Settings)
    (u v : OTerm α) (eq : Derivation body Γ (eqn u v))
    (h : Derivation body Γ (ownBelow V W C s u)) :
    Derivation body Γ (ownBelow V W C s v) := by
  let x : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let θ : Formula (α ⊕ Fin 1) := ownBelow V W C s x
  have inst (t : OTerm α) : instantiate θ (emb t) = ownBelow V W C s t := by
    change instantiate (below (ownMotive V W C s) x) (emb t) = _
    rw [instantiate,bindEmbedding,belowSubst]
    unfold ownMotive
    rw [ownAtSubst] <;> rfl
  have moved := Derivation.equalityElimination θ (emb u) (emb v) eq (by rw [inst]; exact h)
  rw [inst] at moved
  exact moved

theorem moveWindowType (W : Program 3) (ctx ty actual key : OTerm α)
    (eq : Derivation body Γ (eqn ty actual))
    (h : Nonempty (Derivation body Γ (windowAt W ctx ty key))) :
    Nonempty (Derivation body Γ (windowAt W ctx actual key)) := by
  let j : α → α ⊕ Fin 1 := Sum.inl
  let θ := windowAt W (ctx.relabel j) (.var (.inr 0)) (key.relabel j)
  have inst (x : OTerm α) : instantiate θ (emb x) = windowAt W ctx x key := by
    simp only [θ,j,instantiate,bindEmbedding,windowSubst,liftBind,varBind]
  obtain ⟨h⟩ := h
  have moved := Derivation.equalityElimination θ (emb ty) (emb actual) eq (by rw [inst]; exact h)
  rw [inst] at moved
  exact ⟨moved⟩

theorem moveMemberKey (out u v : OTerm α) (eq : Derivation body Γ (eqn u v))
    (h : Nonempty (Derivation body Γ (memberGraph out u))) :
    Nonempty (Derivation body Γ (memberGraph out v)) := by
  let θ : Formula (α ⊕ Fin 1) := memberGraph (out.relabel Sum.inl) (.var (.inr 0))
  have inst (x : OTerm α) : instantiate θ (emb x) = memberGraph out x := by
    simp only [θ,instantiate,bindEmbedding,memberSubst,liftBind,varBind]
  obtain ⟨h⟩ := h
  have moved := Derivation.equalityElimination θ (emb u) (emb v) eq (by rw [inst]; exact h)
  rw [inst] at moved
  exact ⟨moved⟩

theorem renameRow (P : Programs) (s : Settings) (j : α → β) (keep : ∀ f ∈ Γ, f.relabel j ∈ Δ)
    {key p vertices ctx result : OTerm α} (row : ParentRow P s body Γ key p vertices ctx result) :
    ParentRow P s body Δ (key.relabel j) (p.relabel j) (vertices.relabel j) (ctx.relabel j) (result.relabel j) := by
  have typed := renameInto row.typed j Δ keep
  have hbelow := renameInto row.branchBelow j Δ keep
  rw [windowRename] at typed
  rw [ownBelowRename] at hbelow
  exact ⟨moveParent P.V P.R s j keep row.parent,typed,hbelow⟩

theorem packRow (P : Programs) (s : Settings)
    {raw key p vertices ctx result : OTerm α} {tag : Nat} {fields : List (OTerm α)}
    (row : ParentRow P s body Γ raw p vertices ctx result)
    (ordered : Reports body Γ raw NumberedWindowInternalSparseFieldCell.cellTail fields)
    (same : Nonempty (Derivation body Γ (eqn raw key)))
    (header : Nonempty (Derivation body Γ (NumberedWindowInternalCoverSelectedValidityTargets.headerAt tag fields.length raw))) :
    PackedRow P s body Γ raw key p vertices ctx result tag fields := by
  have equality := same
  obtain ⟨e⟩ := equality
  obtain ⟨typed⟩ := row.typed
  obtain ⟨hbelow⟩ := row.branchBelow
  have valid := moveUnary P.V (suc z) raw key same row.parent.valid
  have measured := moveUnary (selectedMeasure P.R) p raw key same row.parent.measured
  have held := moveUnary (scratchVertices P.cover s) vertices raw key same row.parent.held
  have typed' := moveGuard P.W ctx result raw key e typed
  have hbelow' := moveBelow P.V P.W P.cover s raw key e hbelow
  exact ⟨⟨⟨valid,measured,held⟩,typed',⟨hbelow'⟩⟩,ordered,same,header⟩

#print axioms packRow

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverRefinedInductionDispatchTransportProof
