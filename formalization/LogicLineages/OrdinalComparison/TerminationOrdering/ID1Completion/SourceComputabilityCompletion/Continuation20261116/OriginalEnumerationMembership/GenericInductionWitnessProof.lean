module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.GenericInductionMatrixSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.GenericInductionWitnessProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors (graph2)
open InternalTagArithmeticSyntaxProof (emb zSubst sucSubst)
open SourceComputabilityFormulaSupportProof (numeral)
open InternalTermSubstitutionProof InternalFiniteBlocksSubstitutionProof InternalBinderTransportProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalSourceIntroductionSyntaxProof InternalAdditionLawsProof
open InternalRawListRecursionSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
attribute [local irreducible] programGraph
/-- Generic syntactic witness elimination; all program ASTs and Meaning are opaque parameters. -/
theorem witness {alpha : Type} (pair enum member : Program 2)
    (fuel node param p2 p3 out raw bound types heads labels tupleBound : OTerm alpha)
    (meaning : Formula (alpha ⊕ Fin 11)) (meaning' : Formula alpha)
    (hm : meaning.subst (fun a => emb (Sum.elim Term.var
      (![node,param,p2,p3,out,raw,bound,types,heads,labels,tupleBound] : Fin 11 → OTerm alpha) a)) = meaning') :
    (GenericInductionMatrixSyntaxProof.matrix pair enum member fuel meaning).subst
      (Sum.elim Term.var (fun i => emb ((![node,param,p2,p3,out,raw,bound,types,heads,labels,tupleBound] : Fin 11 → OTerm alpha) i))) =
    (graph2 pair node bound fuel ⊓ graph2 pair param types p2 ⊓
      graph2 pair p2 heads p3 ⊓ graph2 pair p3 labels tupleBound ⊓
      graph2 enum out node param).imp
      ((graph2 member (numeral 1) out raw).imp meaning' ⊓
        meaning'.imp (graph2 member (numeral 1) out raw)) := by
  have he : (Sum.elim Term.var (fun i => emb ((![node,param,p2,p3,out,raw,bound,types,heads,labels,tupleBound] : Fin 11 → OTerm alpha) i))) =
      (fun a => emb (Sum.elim Term.var (![node,param,p2,p3,out,raw,bound,types,heads,labels,tupleBound] : Fin 11 → OTerm alpha) a)) := by
    funext a
    cases a <;> rfl
  rw [he]
  unfold GenericInductionMatrixSyntaxProof.matrix
  simp only [impSubst,conjunctionSubst,hm,InternalApplicationValidityStackAppendSyntaxProof.graph2Subst,
    SourceComputabilityFormulaSupportProof.numeral,zSubst,sucSubst,
    witnessLift,Term.subst,Sum.elim_inr]
  all_goals rfl
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.GenericInductionWitnessProof
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.GenericInductionWitnessProof
