module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalPreservationLambdaParameterProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalPreservationLambdaProof
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
open InternalAcceptanceSupportProof (programCases)
theorem atFields (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
 (compat : Compatible p H G W)
 (q input out parameter d e child arrow childParameter : OTerm alpha)
 (hb : Nonempty (Derivation body Delta (belowPayload p H G W P q)))
 (hraw : Nonempty (Derivation body Delta (graph1 InternalUnpair.right q input)))
 (hp : Nonempty (Derivation body Delta (Premises p H G W P input out parameter)))
 (hsf : Nonempty (Derivation body Delta (OriginalLambdaConstructor.Fields input d e child arrow)))
 (hf : Nonempty (Derivation body Delta (LambdaFields input d e child parameter childParameter))) :
 Nonempty (Derivation body Delta (Result p H G W input out parameter)) := by
 apply EvaluatorKeyCanonicalPreservationLambdaQueriesProof.childCases p H G W P
   q input d e child parameter childParameter _ hraw hf
 intro beta j Theta childPayload childOut hj hr hlt hc
 rw [resultRename]
 have hb' := renameInto hb j Theta hj
 have hp' := renameInto hp j Theta hj
 have hsf' := renameInto hsf j Theta hj
 have hf' := renameInto hf j Theta hj
 rw [belowPayloadRename] at hb'
 rw [premisesRename] at hp'
 rw [OriginalLambdaConstructorGraphSyntaxProof.fieldsRename] at hsf'
 rw [lambdaFieldsRename] at hf'
 exact EvaluatorKeyCanonicalPreservationLambdaParameterProof.atOutput p H G W P compat
   (q.relabel j) (input.relabel j) (out.relabel j) (parameter.relabel j) (d.relabel j) (e.relabel j)
   (child.relabel j) (arrow.relabel j) (childParameter.relabel j) childPayload childOut hb' hp' hsf' hf' hr hlt hc

theorem atSourceFields (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
 (compat : Compatible p H G W)
 (q input out parameter d e child arrow : OTerm alpha)
 (hb : Nonempty (Derivation body Delta (belowPayload p H G W P q)))
 (hraw : Nonempty (Derivation body Delta (graph1 InternalUnpair.right q input)))
 (hp : Nonempty (Derivation body Delta (Premises p H G W P input out parameter)))
 (hsf : Nonempty (Derivation body Delta (OriginalLambdaConstructor.Fields input d e child arrow))) :
 Nonempty (Derivation body Delta (Result p H G W input out parameter)) := by
 apply programCases OriginalLambdaTraversal.childParameter (Fin.cons input (Fin.cons parameter Fin.elim0)) _
 intro beta j Theta childParameter hj hcp
 rw [resultRename]
 simp only [consTermRename,emptyRename] at hcp
 have hb' := renameInto hb j Theta hj
 have hr' := renameInto hraw j Theta hj
 have hp' := renameInto hp j Theta hj
 have hsf' := renameInto hsf j Theta hj
 rw [belowPayloadRename] at hb'
 rw [graph1Rename] at hr'
 rw [premisesRename] at hp'
 rw [OriginalLambdaConstructorGraphSyntaxProof.fieldsRename] at hsf'
 have hf := EvaluatorKeyCanonicalPreservationLambdaSupportProof.fieldsAtParameter
   (input.relabel j) (d.relabel j) (e.relabel j) (child.relabel j) (arrow.relabel j)
   (parameter.relabel j) childParameter hsf' hcp
 exact atFields p H G W P compat (q.relabel j) (input.relabel j) (out.relabel j) (parameter.relabel j)
   (d.relabel j) (e.relabel j) (child.relabel j) (arrow.relabel j) childParameter hb' hr' hp' hsf' hf

theorem atTag (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
 (compat : Compatible p H G W)
 (q input out parameter : OTerm alpha)
 (hb : Nonempty (Derivation body Delta (belowPayload p H G W P q)))
 (hraw : Nonempty (Derivation body Delta (graph1 InternalUnpair.right q input)))
 (hp : Nonempty (Derivation body Delta (Premises p H G W P input out parameter)))
 (ht : Nonempty (Derivation body Delta (graph1 OriginalLambdaTraversal.rawTag InternalOriginalStepGuard.one input))) :
 Nonempty (Derivation body Delta (Result p H G W input out parameter)) := by
 have hs := andRight (EvaluatorKeyDomainClosureSupportProof.factors p H G W input parameter (andLeft hp))
 apply OriginalPackedSourceLambdaFieldsProof.actualFieldsCases body alpha Delta H G (member p H G W) W
   input parameter _ hs ht
 intro beta j Theta d e child arrow hj hf
 rw [resultRename]
 have hb' := renameInto hb j Theta hj
 have hr' := renameInto hraw j Theta hj
 have hp' := renameInto hp j Theta hj
 rw [belowPayloadRename] at hb'
 rw [graph1Rename] at hr'
 rw [premisesRename] at hp'
 exact atSourceFields p H G W P compat (q.relabel j) (input.relabel j) (out.relabel j)
   (parameter.relabel j) d e child arrow hb' hr' hp' hf
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalPreservationLambdaProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalPreservationLambdaProof
