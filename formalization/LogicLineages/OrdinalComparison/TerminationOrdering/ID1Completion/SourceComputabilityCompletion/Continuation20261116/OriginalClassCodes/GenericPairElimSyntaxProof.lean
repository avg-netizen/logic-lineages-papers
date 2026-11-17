module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.GenericPairImageSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.GenericPairElimSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors (graph2)
open InternalTagArithmeticSyntaxProof (emb zSubst sucSubst)
open SourceComputabilityFormulaSupportProof (numeral)
open InternalTermSubstitutionProof InternalFiniteBlocksSubstitutionProof InternalBinderTransportProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalSourceIntroductionSyntaxProof InternalAdditionLawsProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
attribute [local irreducible] programGraph
/-- Proof-only matrix with the original five slots, including its unused slots. -/
def matrix {alpha : Type} (roots member pair : Program 2) (raw : OTerm alpha) : Formula (alpha ⊕ Fin 5) :=
  (graph2 roots (.var (.inr 1)) (raw.relabel Sum.inl) (.var (.inr 0)) ⊓
    graph2 member (numeral 1) (.var (.inr 1)) (.var (.inr 2))).imp
      (GenericPairImageSyntaxProof.image member pair (raw.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 2)))

theorem allSubst {alpha beta : Type} (roots member pair : Program 2)
    (raw : OTerm alpha) (ts : alpha → OTerm beta) :
    (InternalClosedPrograms.allBlock (matrix roots member pair raw)).subst (fun a => emb (ts a)) =
      InternalClosedPrograms.allBlock (matrix roots member pair (raw.subst ts)) := by
  rw [allBlockSubst,liftedEmbedding]
  unfold matrix
  simp only [impSubst,conjunctionSubst,GenericPairImageSyntaxProof.imageSubst,
    InternalApplicationValidityStackAppendSyntaxProof.graph2Subst,
    SourceComputabilityFormulaSupportProof.numeral,zSubst,sucSubst,liftSubst,Term.subst,Sum.elim_inr]

theorem witness {alpha : Type} (roots member pair : Program 2)
    (raw param out node sourceChild targetChild : OTerm alpha) :
    (matrix roots member pair raw).subst (Sum.elim Term.var
      (fun i => emb ((![param,out,node,sourceChild,targetChild] : Fin 5 → OTerm alpha) i))) =
      (graph2 roots out raw param ⊓ graph2 member (numeral 1) out node).imp
        (GenericPairImageSyntaxProof.image member pair raw param node) := by
  have he : (Sum.elim Term.var (fun i => emb ((![param,out,node,sourceChild,targetChild] : Fin 5 → OTerm alpha) i))) =
      (fun a => emb (Sum.elim Term.var (![param,out,node,sourceChild,targetChild] : Fin 5 → OTerm alpha) a)) := by
    funext a
    cases a <;> rfl
  rw [he]
  unfold matrix
  simp only [impSubst,conjunctionSubst,GenericPairImageSyntaxProof.imageSubst,
    InternalApplicationValidityStackAppendSyntaxProof.graph2Subst,
    SourceComputabilityFormulaSupportProof.numeral,zSubst,sucSubst,witnessLift,Term.subst,Sum.elim_inr]
  rfl
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.GenericPairElimSyntaxProof
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.GenericPairElimSyntaxProof
