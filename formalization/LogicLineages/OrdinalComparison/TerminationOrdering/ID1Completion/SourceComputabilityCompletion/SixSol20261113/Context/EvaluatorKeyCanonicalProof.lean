module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalInductionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof (programCases)
open InternalApplicationStepPeelSupportProof (andIntro)
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalRecursionGraphStepSyntaxProof
open EvaluatorKeyCanonicalInductionDefinitions EvaluatorKeyCanonicalSyntaxProof
attribute [local irreducible] programGraph
theorem actualCanonicalEquality : EvaluatorKeyCanonicalTargets.ActualCanonicalEquality := by
 intro p H G W P body alpha Delta left right leftOut rightOut parameter
 dsimp only
 intro dl dr same cl cr
 have hp : Nonempty (Derivation body Delta (Premises p H G W P left right leftOut rightOut parameter)) :=
   andIntro dl (andIntro dr (andIntro same (andIntro cl cr)))
 apply programCases InternalUnpair.right (Fin.cons left Fin.elim0) _
 intro beta j Theta q hj hraw
 have hp' := renameInto hp j Theta hj
 rw [premisesRename] at hp'
 simp only [consTermRename,emptyRename] at hraw
 rw [equalEqn,InternalTagArithmeticSyntaxProof.eqnRelabel,← equalEqn]
 exact EvaluatorKeyCanonicalBindingProof.atPayloadApply p H G W P q (left.relabel j) (right.relabel j)
   (leftOut.relabel j) (rightOut.relabel j) (parameter.relabel j)
   (EvaluatorKeyCanonicalInductionProof.actualAll p H G W P body beta Theta q) hraw hp'
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalProof
