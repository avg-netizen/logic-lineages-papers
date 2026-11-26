module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalPreservationLambdaAssemblyProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalPreservationLambdaParameterProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalApplicationStepPeelSupportProof (andLeft andRight andIntro)
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalRecursionGraphStepSyntaxProof
open OriginalLambdaTraversalInternal OriginalLambdaTraversalInternalFieldsSyntaxProof
open UniformCertificateCompletion EvaluatorKeyPut
open EvaluatorKeyCanonicalInductionDefinitions (C)
open EvaluatorKeyCanonicalPreservationInductionDefinitions EvaluatorKeyCanonicalPreservationDefinitions
open EvaluatorKeyCanonicalPreservationSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
theorem atOutput (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
 (compat : Compatible p H G W)
 (q input out parameter d e child arrow childParameter childPayload childOut : OTerm alpha)
 (hb : Nonempty (Derivation body Delta (belowPayload p H G W P q)))
 (hp : Nonempty (Derivation body Delta (Premises p H G W P input out parameter)))
 (hsf : Nonempty (Derivation body Delta (OriginalLambdaConstructor.Fields input d e child arrow)))
 (hf : Nonempty (Derivation body Delta (LambdaFields input d e child parameter childParameter)))
 (hr : Nonempty (Derivation body Delta (graph1 InternalUnpair.right childPayload child)))
 (hlt : Nonempty (Derivation body Delta (InternalLessThan.strictLess childPayload q)))
 (hc : Nonempty (Derivation body Delta (graph2 (C p H G W P) childOut child childParameter)))
 : Nonempty (Derivation body Delta (Result p H G W input out parameter)) := by
 let gp : Program 2 := rightOf (.projection 1)
 let qs : Fin 3 → Program 2 := ![leftOf (.projection 1),gp,consOf (.projection 0) gp]
 let xs : Fin 2 → OTerm alpha := ![d,parameter]
 apply OriginalRawSyntaxTransportInternalParserSupportProof.programsCases qs xs _
 intro beta j Theta ys hj hg
 rw [resultRename]
 have hx : (fun i => (xs i).relabel j) = (![d.relabel j,parameter.relabel j] : Fin 2 → OTerm beta) := by
   funext i
   exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) i
 rw [hx] at hg
 let xx : Fin 2 → OTerm beta := ![d.relabel j,parameter.relabel j]
 have hpl := unaryRecover InternalUnpair.left (.projection 1) (ys 0) (parameter.relabel j) xx (hg 0) (projectionValue 1 xx)
 have hpr := unaryRecover InternalUnpair.right (.projection 1) (ys 1) (parameter.relabel j) xx (hg 1) (projectionValue 1 xx)
 have hparam := reconstructPair (parameter.relabel j) (ys 0) (ys 1) hpl hpr
 have hcons := binaryRecover InternalListCodec.consCode (.projection 0) gp (ys 2) (d.relabel j) (ys 1)
   xx (hg 2) (projectionValue 0 xx) (hg 1)
 have hb' := renameInto hb j Theta hj
 have hp' := renameInto hp j Theta hj
 have hsf' := renameInto hsf j Theta hj
 have hf' := renameInto hf j Theta hj
 have hr' := renameInto hr j Theta hj
 have hlt' := renameInto hlt j Theta hj
 have hc' := renameInto hc j Theta hj
 rw [belowPayloadRename] at hb'
 rw [premisesRename] at hp'
 rw [OriginalLambdaConstructorGraphSyntaxProof.fieldsRename] at hsf'
 rw [lambdaFieldsRename] at hf'
 rw [graph1Rename] at hr'
 rw [graph2Rename] at hc'
 simp only [InternalLessThan.strictLess,InternalOriginalOrderSyntaxProof.orderRename] at hlt'
 exact EvaluatorKeyCanonicalPreservationLambdaAssemblyProof.atCoordinates p H G W P compat
   (q.relabel j) (input.relabel j) (out.relabel j) (parameter.relabel j) (d.relabel j) (e.relabel j) (child.relabel j) (arrow.relabel j) (childParameter.relabel j) (childPayload.relabel j) (childOut.relabel j) (ys 0) (ys 1) (ys 2)
   hb' hp' hsf' hf' hr' hlt' hc' hparam hcons
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalPreservationLambdaParameterProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalPreservationLambdaParameterProof
