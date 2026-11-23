module

public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedScratchMemberTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathSuccessfulAdvanceGraphSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphStepSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionLawsProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedScratchMemberSyntaxProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalApplicationCertificateConstructors (graph2)
open ID1Completion.InternalApplicationValidityStackAppendSyntaxProof (graph2Subst)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open ID1Completion.InternalRecursionClosureSyntaxProof (conjunctionSubst)
open ID1Completion.InternalAdditionLawsProof (impSubst)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb bindEmbedding liftBind varBind sucRelabel zRelabel sucSubst zSubst)
open ID1Completion.InternalListInduction (atCode atIndex)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (unary suc z)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparsePathSuccessfulAdvanceGraphSyntaxProof (unarySubst)
open NumberedWindowInternalSparseScratchMembership (scratchMember)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalDirectBoundaryGuardsTargets (typedScratch)
open NumberedWindowInternalDirectTypedScratchMemberTargets

private theorem memberGraph2 {α : Type} (code key : OTerm α) :
    memberGraph code key = graph2 scratchMember (suc z) code key := by
  have tape : (![code,key] : Fin 2 → OTerm α) = Fin.cons code (Fin.cons key Fin.elim0) := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) i
  unfold memberGraph
  rw [tape]

private theorem fromRename {α β : Type} (i : Program 1) (code key : OTerm α) (ρ : α → β) :
    (fromMember i code key).relabel ρ = fromMember i (code.relabel ρ) (key.relabel ρ) := by
  unfold fromMember
  change ((unary (typedScratch i) (suc z) code ⊓ memberGraph code key).relabel ρ).imp
    ((unary i (suc z) key).relabel ρ) = _
  simp only [conjunctionRename,unaryRename,graphRename,sucRelabel,zRelabel]

private theorem fromSubst {α β : Type} (i : Program 1) (code key : OTerm α) (σ : α → OTerm β) :
    (fromMember i code key).subst (fun a => emb (σ a)) =
      fromMember i (code.subst σ) (key.subst σ) := by
  simp only [fromMember,impSubst,conjunctionSubst,unarySubst,memberGraph2,graph2Subst,sucSubst,zSubst]

theorem invariantCode {α : Type} (i : Program 1) (key code : OTerm α) :
    atCode (invariant i key) code = fromMember i code key := by
  rw [atCode,instantiate,bindEmbedding]
  change (fromMember i (.var (.inr 0) : OTerm (α ⊕ Fin 1)) (key.relabel Sum.inl)).subst _ = _
  rw [fromSubst]
  simp only [liftBind,varBind]

theorem invariantIndex {α : Type} (i : Program 1) (key : OTerm α) (j : Fin 3) :
    atIndex (invariant i key) j = fromMember i (.var (.inr j)) (key.relabel Sum.inl) := by
  unfold atIndex
  change (fromMember i (.var (.inr 0) : OTerm (α ⊕ Fin 1)) (key.relabel Sum.inl)).relabel _ = _
  rw [fromRename]
  simp only [Term.relabel_relabel,Term.relabel] <;> rfl

end LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedScratchMemberSyntaxProof
