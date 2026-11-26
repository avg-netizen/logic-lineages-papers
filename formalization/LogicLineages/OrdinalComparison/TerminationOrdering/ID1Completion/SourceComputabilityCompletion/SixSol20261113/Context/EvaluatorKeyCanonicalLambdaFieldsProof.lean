module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalLambdaQueriesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalPayloadLambdaProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalLambdaFieldsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalRecursionGraphStepSyntaxProof
open OriginalLambdaTraversalInternal OriginalLambdaTraversalInternalFieldsSyntaxProof
open UniformCertificateCompletion EvaluatorKeyPut EvaluatorKeyCanonicalInductionDefinitions EvaluatorKeyCanonicalSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
theorem atSameFields (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
 (q left right leftOut rightOut parameter domain codomain child otherChild childParameter : OTerm alpha)
 (hb : Nonempty (Derivation body Delta (belowPayload p H G W P q)))
 (hraw : Nonempty (Derivation body Delta (graph1 InternalUnpair.right q left)))
 (hp : Nonempty (Derivation body Delta (Premises p H G W P left right leftOut rightOut parameter)))
 (hl : Nonempty (Derivation body Delta (LambdaFields left domain codomain child parameter childParameter)))
 (hr : Nonempty (Derivation body Delta (LambdaFields right domain codomain otherChild parameter childParameter))) :
 Nonempty (Derivation body Delta (equal leftOut rightOut)) := by
 apply OriginalLambdaTraversalInternalPayloadLambdaProof.lambdaPayloadCases left child q _
   (andLeft (andRight (andRight (andRight hl)))) hraw (andLeft hl)
 intro beta j Theta childPayload hj hc hbound
 have hb' := renameInto hb j Theta hj
 have hp' := renameInto hp j Theta hj
 have hl' := renameInto hl j Theta hj
 have hr' := renameInto hr j Theta hj
 rw [belowPayloadRename] at hb'
 rw [premisesRename] at hp'
 rw [lambdaFieldsRename] at hl' hr'
 rw [equalEqn,InternalTagArithmeticSyntaxProof.eqnRelabel,← equalEqn]
 exact EvaluatorKeyCanonicalLambdaQueriesProof.atPayload p H G W P (q.relabel j) (left.relabel j) (right.relabel j)
   (leftOut.relabel j) (rightOut.relabel j) (parameter.relabel j) (domain.relabel j) (codomain.relabel j)
   (child.relabel j) (otherChild.relabel j) (childParameter.relabel j) childPayload hb' hp' hl' hr' hc
   (OriginalLambdaTraversalInternalPayloadArithmeticProof.lambdaDescent _ _ hbound)
theorem atFields (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
 (q left right leftOut rightOut parameter ld lc child lp rd rc otherChild rp : OTerm alpha)
 (hb : Nonempty (Derivation body Delta (belowPayload p H G W P q)))
 (hraw : Nonempty (Derivation body Delta (graph1 InternalUnpair.right q left)))
 (hp : Nonempty (Derivation body Delta (Premises p H G W P left right leftOut rightOut parameter)))
 (hl : Nonempty (Derivation body Delta (LambdaFields left ld lc child parameter lp)))
 (hr : Nonempty (Derivation body Delta (LambdaFields right rd rc otherChild parameter rp))) :
 Nonempty (Derivation body Delta (equal leftOut rightOut)) := by
 have had := EvaluatorKeyOtherDomainProof.admitted p H G W left right parameter
   (andLeft hp) (andLeft (andRight hp)) (andLeft (andRight (andRight hp)))
 have he := EvaluatorAlignmentProof.actualLambda (baseRepresentative p H G W) H G (member p H G W) W body alpha Delta
   left right parameter ld lc child lp rd rc otherChild rp had hl hr
 have hr' := EvaluatorKeyCanonicalLambdaSupportProof.alignFields right parameter ld lc otherChild lp rd rc rp hr
   (andLeft he) (andLeft (andRight he)) (andRight (andRight he))
 exact atSameFields p H G W P q left right leftOut rightOut parameter ld lc child otherChild lp hb hraw hp hl hr'
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalLambdaFieldsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalLambdaFieldsProof
