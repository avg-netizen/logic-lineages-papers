module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.GenericPairImageSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors (graph2)
open InternalTagArithmeticSyntaxProof (emb zSubst sucSubst bindEmbedding liftBind varBind)
open SourceComputabilityFormulaSupportProof (numeral existsOne)
open InternalTermSubstitutionProof InternalFiniteBlocksSubstitutionProof InternalBinderTransportProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalSourceIntroductionSyntaxProof InternalAdditionLawsProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
attribute [local irreducible] programGraph
/-- Proof-only schema, with both original programs opaque parameters. -/
def matrix {alpha : Type} (member pair : Program 2) (raw param node : OTerm alpha) : Formula (alpha ⊕ Fin 1) :=
  graph2 member (numeral 1) (raw.relabel Sum.inl) (.var (.inr 0)) ⊓
    graph2 pair (node.relabel Sum.inl) (param.relabel Sum.inl) (.var (.inr 0))
def image {alpha : Type} (member pair : Program 2) (raw param node : OTerm alpha) : Formula alpha :=
  existsOne (matrix member pair raw param node)

theorem imageSubst {alpha beta : Type} (member pair : Program 2)
    (raw param node : OTerm alpha) (ts : alpha → OTerm beta) :
    (image member pair raw param node).subst (fun a => emb (ts a)) =
      image member pair (raw.subst ts) (param.subst ts) (node.subst ts) := by
  unfold image matrix
  rw [existsSubst,liftedEmbedding]
  simp only [conjunctionSubst,InternalApplicationValidityStackAppendSyntaxProof.graph2Subst,
    SourceComputabilityFormulaSupportProof.numeral,zSubst,sucSubst,liftSubst,Term.subst,Sum.elim_inr]

theorem imageWitness {alpha : Type} (member pair : Program 2) (raw param node source : OTerm alpha) :
    InternalCalculus.instantiate (matrix member pair raw param node) (emb source) =
      (graph2 member (numeral 1) raw source ⊓ graph2 pair node param source) := by
  unfold matrix InternalCalculus.instantiate
  rw [bindEmbedding]
  simp only [conjunctionSubst,InternalApplicationValidityStackAppendSyntaxProof.graph2Subst,
    SourceComputabilityFormulaSupportProof.numeral,zSubst,sucSubst,liftBind,varBind]
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.GenericPairImageSyntaxProof
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.GenericPairImageSyntaxProof
