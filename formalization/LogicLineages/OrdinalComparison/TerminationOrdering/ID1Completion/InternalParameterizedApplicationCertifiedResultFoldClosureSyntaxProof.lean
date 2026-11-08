module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationCertifiedResultFoldClosureTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertifiedResultFoldClosureBridgeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultStackCompositionRunProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultStackWiringProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationCertifiedResultFoldClosureSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalParameterizedApplicationCertifiedResultFoldClosure
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open InternalRecursionGraphStepSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

@[simp] theorem certifiedFoldPRename {α β : Type} (guard leaf : Program 2) (combine : Program 5)
    (out value parameter : OTerm α) (j : α → β) :
    (certifiedFoldP guard leaf combine out value parameter).relabel j =
      certifiedFoldP guard leaf combine (out.relabel j) (value.relabel j) (parameter.relabel j) := by
  simp only [certifiedFoldP,conjunctionRename,graph2Rename,
    InternalOriginalStepGuard.one,sucRelabel,zRelabel]

@[simp] theorem leafGraphsPRename {α β : Type} (guard leaf : Program 2)
    (out value parameter : OTerm α) (j : α → β) :
    (leafGraphsP guard leaf out value parameter).relabel j =
      leafGraphsP guard leaf (out.relabel j) (value.relabel j) (parameter.relabel j) := by
  simp only [leafGraphsP,conjunctionRename,graph2Rename,zRelabel]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationCertifiedResultFoldClosureSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationCertifiedResultFoldClosureSyntaxProof
