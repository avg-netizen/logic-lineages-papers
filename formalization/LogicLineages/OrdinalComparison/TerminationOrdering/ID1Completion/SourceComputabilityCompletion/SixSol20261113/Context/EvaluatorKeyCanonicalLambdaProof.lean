module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalLambdaFieldsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorOtherMarksTagTransferProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalLambdaProof
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
theorem atLeftFields (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
 (q left right leftOut rightOut parameter ld lc child lp : OTerm alpha)
 (hb : Nonempty (Derivation body Delta (belowPayload p H G W P q)))
 (hraw : Nonempty (Derivation body Delta (graph1 InternalUnpair.right q left)))
 (hp : Nonempty (Derivation body Delta (Premises p H G W P left right leftOut rightOut parameter)))
 (hl : Nonempty (Derivation body Delta (LambdaFields left ld lc child parameter lp))) :
 Nonempty (Derivation body Delta (equal leftOut rightOut)) := by
 have had := EvaluatorKeyOtherDomainProof.admitted p H G W left right parameter
   (andLeft hp) (andLeft (andRight hp)) (andLeft (andRight (andRight hp)))
 have ht := SixSol20261113.Erasure.EvaluatorOtherMarksTagTransferProof.actualTagTransfer
   (baseRepresentative p H G W) H G (member p H G W) W left right parameter InternalOriginalStepGuard.one had (andLeft hl)
 apply OriginalLambdaTraversalOutputLambdaOpeningProof.lambdaFieldsCases right parameter _ ht
 intro beta j Theta rd rc otherChild rp hj hr
 have hb' := renameInto hb j Theta hj
 have hp' := renameInto hp j Theta hj
 have hraw' := renameInto hraw j Theta hj
 have hl' := renameInto hl j Theta hj
 rw [belowPayloadRename] at hb'
 rw [premisesRename] at hp'
 rw [graph1Rename] at hraw'
 rw [lambdaFieldsRename] at hl'
 rw [equalEqn,InternalTagArithmeticSyntaxProof.eqnRelabel,← equalEqn]
 exact EvaluatorKeyCanonicalLambdaFieldsProof.atFields p H G W P (q.relabel j) (left.relabel j) (right.relabel j)
   (leftOut.relabel j) (rightOut.relabel j) (parameter.relabel j) (ld.relabel j) (lc.relabel j)
   (child.relabel j) (lp.relabel j) rd rc otherChild rp hb' hraw' hp' hl' hr

theorem atTag (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
 (q left right leftOut rightOut parameter : OTerm alpha)
 (hb : Nonempty (Derivation body Delta (belowPayload p H G W P q)))
 (hraw : Nonempty (Derivation body Delta (graph1 InternalUnpair.right q left)))
 (hp : Nonempty (Derivation body Delta (Premises p H G W P left right leftOut rightOut parameter)))
 (ht : Nonempty (Derivation body Delta (graph1 OriginalLambdaTraversal.rawTag InternalOriginalStepGuard.one left))) :
 Nonempty (Derivation body Delta (equal leftOut rightOut)) := by
 apply OriginalLambdaTraversalOutputLambdaOpeningProof.lambdaFieldsCases left parameter _ ht
 intro beta j Theta ld lc child lp hj hl
 have hb' := renameInto hb j Theta hj
 have hp' := renameInto hp j Theta hj
 have hraw' := renameInto hraw j Theta hj
 rw [belowPayloadRename] at hb'
 rw [premisesRename] at hp'
 rw [graph1Rename] at hraw'
 rw [equalEqn,InternalTagArithmeticSyntaxProof.eqnRelabel,← equalEqn]
 exact atLeftFields p H G W P (q.relabel j) (left.relabel j) (right.relabel j)
   (leftOut.relabel j) (rightOut.relabel j) (parameter.relabel j) ld lc child lp hb' hraw' hp' hl
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalLambdaProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalLambdaProof
