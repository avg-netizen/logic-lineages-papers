module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalLambdaCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalOutputLambdaOpeningProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalLambdaQueriesProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalRecursionGraphStepSyntaxProof
open OriginalLambdaTraversalInternal OriginalLambdaTraversalInternalFieldsSyntaxProof
open UniformCertificateCompletion EvaluatorKeyPut EvaluatorKeyCanonicalInductionDefinitions EvaluatorKeyCanonicalSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
theorem atPayload (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
 (q left right leftOut rightOut parameter domain codomain child otherChild childParameter childPayload : OTerm alpha)
 (hb : Nonempty (Derivation body Delta (belowPayload p H G W P q)))
 (hp : Nonempty (Derivation body Delta (Premises p H G W P left right leftOut rightOut parameter)))
 (hl : Nonempty (Derivation body Delta (LambdaFields left domain codomain child parameter childParameter)))
 (hr : Nonempty (Derivation body Delta (LambdaFields right domain codomain otherChild parameter childParameter)))
 (hraw : Nonempty (Derivation body Delta (graph1 InternalUnpair.right childPayload child)))
 (hlt : Nonempty (Derivation body Delta (InternalLessThan.strictLess childPayload q))) :
 Nonempty (Derivation body Delta (equal leftOut rightOut)) := by
 let F := C p H G W P
 let qs : Fin 2 → Program 3 := ![.composition F ![.projection 0,.projection 2],.composition F ![.projection 1,.projection 2] ]
 let xs : Fin 3 → OTerm alpha := ![child,otherChild,childParameter]
 apply OriginalRawSyntaxTransportInternalParserSupportProof.programsCases qs xs _
 intro beta j Theta values hj hg
 have hx : (fun i => (xs i).relabel j) = (![child.relabel j,otherChild.relabel j,childParameter.relabel j] : Fin 3 → OTerm beta) := by
   funext i
   exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))) i
 rw [hx] at hg
 let xx : Fin 3 → OTerm beta := ![child.relabel j,otherChild.relabel j,childParameter.relabel j]
 have hcl := binaryRecover F (.projection 0) (.projection 2) (values 0) (child.relabel j) (childParameter.relabel j) xx (hg 0) (projectionValue 0 xx) (projectionValue 2 xx)
 have hcr := binaryRecover F (.projection 1) (.projection 2) (values 1) (otherChild.relabel j) (childParameter.relabel j) xx (hg 1) (projectionValue 1 xx) (projectionValue 2 xx)
 have hb' := renameInto hb j Theta hj
 have hp' := renameInto hp j Theta hj
 have hl' := renameInto hl j Theta hj
 have hr' := renameInto hr j Theta hj
 have hraw' := renameInto hraw j Theta hj
 have hlt' := renameInto hlt j Theta hj
 rw [belowPayloadRename] at hb'
 rw [premisesRename] at hp'
 rw [lambdaFieldsRename] at hl' hr'
 rw [graph1Rename] at hraw'
 simp only [InternalLessThan.strictLess,InternalOriginalOrderSyntaxProof.orderRename] at hlt'
 rw [equalEqn,InternalTagArithmeticSyntaxProof.eqnRelabel,← equalEqn]
 exact EvaluatorKeyCanonicalLambdaCoreProof.atOutputs p H G W P (q.relabel j) (left.relabel j) (right.relabel j)
   (leftOut.relabel j) (rightOut.relabel j) (parameter.relabel j) (domain.relabel j) (codomain.relabel j)
   (child.relabel j) (otherChild.relabel j) (childParameter.relabel j) (childPayload.relabel j) (values 0) (values 1)
   hb' hp' hl' hr' hraw' hlt' hcl hcr
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalLambdaQueriesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalLambdaQueriesProof
