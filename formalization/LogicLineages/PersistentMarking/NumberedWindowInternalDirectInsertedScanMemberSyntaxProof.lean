module
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectInsertedScanMemberTargets
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphStepSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionLawsProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalDirectInsertedScanMember
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalRawListRecursion (recGraph)
open ID1Completion.InternalApplicationCertificateConstructors (graph2)
open ID1Completion.InternalApplicationCertificateConstructorsSyntaxProof (graph2Rename)
open ID1Completion.InternalApplicationValidityStackAppendSyntaxProof (graph2Subst)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open ID1Completion.InternalRecursionClosureSyntaxProof (conjunctionSubst)
open ID1Completion.InternalAdditionLawsProof (impSubst)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb bindEmbedding liftBind varBind sucRelabel zRelabel sucSubst zSubst)
open ID1Completion.InternalListInduction (atCode atIndex)
open LogicLineages.ComputabilityKnowledge GorbowPRProgram
open NumberedWindowInternalDirectInsertedRowTargets (insertedRow oneTerm)
open NumberedWindowInternalDirectInsertedScanTargets (scanLoop loopAccept rowAccept)
open NumberedWindowInternalSparseScratchMembership (scratchMember)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalDirectInsertedScanMemberTargets
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)

private theorem tapeOne {α : Type} (x : OrdinaryArithmetic.Term α) :
    (![x] : Fin 1 → OrdinaryArithmetic.Term α) = Fin.cons x Fin.elim0 := by
  funext i
  exact Fin.cases rfl (fun j => Fin.elim0 j) i

private theorem tapeTwo {α : Type} (x y : OrdinaryArithmetic.Term α) :
    (![x,y] : Fin 2 → OrdinaryArithmetic.Term α) = Fin.cons x (Fin.cons y Fin.elim0) := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)) i

private theorem loopGraph2 {α : Type} (r : Program 3) (code removed : OrdinaryArithmetic.Term α) :
    loopAccept r code removed = graph2 (scanLoop r) oneTerm code removed := by
  unfold loopAccept recGraph
  rw [tapeOne] <;> rfl

private theorem rowGraph2 {α : Type} (r : Program 3) (row removed : OrdinaryArithmetic.Term α) :
    rowAccept r row removed = graph2 (insertedRow r) oneTerm removed row := by
  unfold rowAccept
  rw [tapeTwo]

private theorem memberGraph2 {α : Type} (code k : OrdinaryArithmetic.Term α) :
    memberGraph code k = graph2 scratchMember (suc z) code k := by
  unfold memberGraph
  rw [tapeTwo]

private theorem fromRename {α β : Type} (r : Program 3)
    (code removed k : OrdinaryArithmetic.Term α) (ρ : α → β) :
    (fromMember r code removed k).relabel ρ =
      fromMember r (code.relabel ρ) (removed.relabel ρ) (k.relabel ρ) := by
  unfold fromMember
  change ((loopAccept r code removed ⊓ memberGraph code k).relabel ρ).imp
    ((rowAccept r k removed).relabel ρ) = _
  simp only [conjunctionRename,loopGraph2,rowGraph2,memberGraph2,graph2Rename,oneTerm,sucRelabel,zRelabel]

private theorem fromSubst {α β : Type} (r : Program 3)
    (code removed k : OrdinaryArithmetic.Term α) (σ : α → OrdinaryArithmetic.Term β) :
    (fromMember r code removed k).subst (fun a => emb (σ a)) =
      fromMember r (code.subst σ) (removed.subst σ) (k.subst σ) := by
  simp only [fromMember,impSubst,conjunctionSubst,loopGraph2,rowGraph2,memberGraph2,
    graph2Subst,oneTerm,sucSubst,zSubst]

theorem invariantCode {α : Type} (r : Program 3) (removed k code : OrdinaryArithmetic.Term α) :
    atCode (invariant r removed k) code = fromMember r code removed k := by
  rw [atCode,instantiate,bindEmbedding]
  change (fromMember r (.var (.inr 0) : OrdinaryArithmetic.Term (α ⊕ Fin 1))
    (removed.relabel Sum.inl) (k.relabel Sum.inl)).subst _ = _
  rw [fromSubst]
  simp only [liftBind,varBind]

theorem invariantIndex {α : Type} (r : Program 3) (removed k : OrdinaryArithmetic.Term α) (i : Fin 3) :
    atIndex (invariant r removed k) i =
      fromMember r (.var (.inr i)) (removed.relabel Sum.inl) (k.relabel Sum.inl) := by
  unfold atIndex
  change (fromMember r (.var (.inr 0) : OrdinaryArithmetic.Term (α ⊕ Fin 1))
    (removed.relabel Sum.inl) (k.relabel Sum.inl)).relabel _ = _
  rw [fromRename]
  simp only [Term.relabel_relabel,Term.relabel] <;> rfl

end LogicLineages.PersistentMarking.NumberedWindowInternalDirectInsertedScanMember
