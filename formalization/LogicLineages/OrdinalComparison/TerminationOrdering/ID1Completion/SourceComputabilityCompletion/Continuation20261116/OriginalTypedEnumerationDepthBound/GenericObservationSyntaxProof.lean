module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityApplicationSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.GenericObservationSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalTagArithmeticSyntaxProof hiding OTerm
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalRawListRecursionSyntaxProof (consTermSubst emptySubst)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
attribute [local irreducible] programGraph

/-- Substitution for the unchanged five observations, abstracting only executable
program parameters during the syntactic proof to bound elaboration memory. -/
theorem observationsSubst {alpha beta : Type} (C B D : Program 1) (P : Program 2)
    (raw : OTerm alpha) (xs : Fin 6 → OTerm alpha) (A : Formula alpha) (A' : Formula beta)
    (ts : alpha → OTerm beta) (ha : A.subst (fun a => emb (ts a)) = A') :
    (graph1 C (numeral 1) raw ⊓ A ⊓ graph1 B (xs 2) raw ⊓
      graph2 P (xs 2) (xs 3) (xs 4) ⊓ graph1 D (xs 5) raw).subst (fun a => emb (ts a)) =
    (graph1 C (numeral 1) (raw.subst ts) ⊓ A' ⊓ graph1 B ((xs 2).subst ts) (raw.subst ts) ⊓
      graph2 P ((xs 2).subst ts) ((xs 3).subst ts) ((xs 4).subst ts) ⊓ graph1 D ((xs 5).subst ts) (raw.subst ts)) := by
  simp only [conjunctionSubst,ha,graph1,graph2,
    InternalComputabilityApplicationSyntaxProof.programSubst,consTermSubst,emptySubst,numeral,sucSubst,zSubst]
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.GenericObservationSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.GenericObservationSyntaxProof
