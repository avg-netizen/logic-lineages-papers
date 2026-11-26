module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalPreservationApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalPreservationLambdaProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalPreservationOtherProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalTagCasesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalPreservationStepProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open InternalGraphCompositionFunctionalityProof (renameInto)
open UniformCertificateCompletion
open EvaluatorKeyCanonicalPreservationInductionDefinitions EvaluatorKeyCanonicalPreservationSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem actualStep (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
 (compat : EvaluatorKeyCanonicalPreservationDefinitions.Compatible p H G W)
 (q input out parameter : OTerm alpha)
 (hb : Nonempty (Derivation body Delta (belowPayload p H G W P q)))
 (hraw : Nonempty (Derivation body Delta (graph1 InternalUnpair.right q input)))
 (hp : Nonempty (Derivation body Delta (Premises p H G W P input out parameter))) :
 Nonempty (Derivation body Delta (Result p H G W input out parameter)) := by
 apply OriginalLambdaTraversalTagCasesProof.tagCases input _
 · intro beta j Theta hj ht
   rw [resultRename]
   have hb' := renameInto hb j Theta hj
   have hp' := renameInto hp j Theta hj
   have hr' := renameInto hraw j Theta hj
   rw [belowPayloadRename] at hb'
   rw [premisesRename] at hp'
   rw [graph1Rename] at hr'
   exact EvaluatorKeyCanonicalPreservationApplicationProof.atTag p H G W P compat
    (q.relabel j) (input.relabel j) (out.relabel j) (parameter.relabel j) hb' hr' hp' ht
 · intro beta j Theta hj ht
   rw [resultRename]
   have hb' := renameInto hb j Theta hj
   have hp' := renameInto hp j Theta hj
   have hr' := renameInto hraw j Theta hj
   rw [belowPayloadRename] at hb'
   rw [premisesRename] at hp'
   rw [graph1Rename] at hr'
   exact EvaluatorKeyCanonicalPreservationLambdaProof.atTag p H G W P compat
    (q.relabel j) (input.relabel j) (out.relabel j) (parameter.relabel j) hb' hr' hp' ht
 · intro beta j Theta hj ht
   rw [resultRename]
   have hp' := renameInto hp j Theta hj
   rw [premisesRename] at hp'
   exact EvaluatorKeyCanonicalPreservationOtherProof.atOther p H G W P
    (input.relabel j) (out.relabel j) (parameter.relabel j) (andLeft hp') (andRight hp') ht
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalPreservationStepProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalPreservationStepProof
