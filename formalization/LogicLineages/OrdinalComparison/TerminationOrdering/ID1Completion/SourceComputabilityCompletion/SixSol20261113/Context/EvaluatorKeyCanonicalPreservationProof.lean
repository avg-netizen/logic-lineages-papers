module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalPreservationInductionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalPreservationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalAcceptanceSupportProof (programCases)
open InternalApplicationStepPeelSupportProof (andIntro)
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalRecursionGraphStepSyntaxProof
open InternalControlGraphSupportProof (emptyRename)
open EvaluatorKeyCanonicalPreservationInductionDefinitions EvaluatorKeyCanonicalPreservationSyntaxProof
attribute [local irreducible] programGraph
theorem actualConditionalPreservation : EvaluatorKeyCanonicalPreservationTargets.ActualConditionalPreservation := by
 intro p H G W P compat body alpha Delta input out parameter hd hc
 have hp : Nonempty (Derivation body Delta (Premises p H G W P input out parameter)) := andIntro hd hc
 change Nonempty (Derivation body Delta (Result p H G W input out parameter))
 apply programCases InternalUnpair.right (Fin.cons input Fin.elim0) _
 intro beta j Theta q hj hraw
 rw [resultRename]
 have hp' := renameInto hp j Theta hj
 rw [premisesRename] at hp'
 simp only [consTermRename,emptyRename] at hraw
 exact EvaluatorKeyCanonicalPreservationBindingProof.atPayloadApply p H G W P q
  (input.relabel j) (out.relabel j) (parameter.relabel j)
  (EvaluatorKeyCanonicalPreservationInductionProof.actualAll p H G W P compat body beta Theta q) hraw hp'
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalPreservationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalPreservationProof
