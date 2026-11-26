module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.GenericListMatrixSyntaxProof
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
/-- Proof-only generic one-binder equivalence matrix. -/
def matrix {alpha : Type} (member : Program 2) (list : OTerm alpha)
    (meaning : Formula (alpha ⊕ Fin 1)) : Formula (alpha ⊕ Fin 1) :=
  let membership := graph2 member (numeral 1) (list.relabel Sum.inl) (.var (.inr 0))
  membership.imp meaning ⊓ meaning.imp membership

theorem allSubst {alpha beta : Type} (member : Program 2) (list : OTerm alpha)
    (ts : alpha → OTerm beta) (meaning : Formula (alpha ⊕ Fin 1)) (meaning' : Formula (beta ⊕ Fin 1))
    (hm : meaning.subst (fun a => emb (Sum.elim (fun x => (ts x).relabel Sum.inl)
      (fun i : Fin 1 => (.var (.inr i) : OTerm (beta ⊕ Fin 1))) a)) = meaning') :
    (InternalClosedPrograms.allBlock (matrix member list meaning)).subst (fun a => emb (ts a)) =
      InternalClosedPrograms.allBlock (matrix member (list.subst ts) meaning') := by
  rw [allBlockSubst,liftedEmbedding]
  unfold matrix
  simp only [conjunctionSubst,impSubst,hm,InternalApplicationValidityStackAppendSyntaxProof.graph2Subst,
    SourceComputabilityFormulaSupportProof.numeral,zSubst,sucSubst,liftSubst,Term.subst,Sum.elim_inr]

theorem witness {alpha : Type} (member : Program 2) (list raw : OTerm alpha)
    (meaning : Formula (alpha ⊕ Fin 1)) (meaning' : Formula alpha)
    (hm : meaning.subst (fun a => emb (Sum.elim Term.var (fun _ : Fin 1 => raw) a)) = meaning') :
    (matrix member list meaning).subst (Sum.elim Term.var (fun _ : Fin 1 => emb raw)) =
      (graph2 member (numeral 1) list raw).imp meaning' ⊓
        meaning'.imp (graph2 member (numeral 1) list raw) := by
  have he : (Sum.elim Term.var (fun _ : Fin 1 => emb raw)) =
      (fun a => emb (Sum.elim Term.var (fun _ : Fin 1 => raw) a)) := by
    funext a
    cases a <;> rfl
  rw [he]
  unfold matrix
  simp only [conjunctionSubst,impSubst,hm,InternalApplicationValidityStackAppendSyntaxProof.graph2Subst,
    SourceComputabilityFormulaSupportProof.numeral,zSubst,sucSubst,witnessLift,Term.subst,Sum.elim_inr]
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.GenericListMatrixSyntaxProof
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.GenericListMatrixSyntaxProof
