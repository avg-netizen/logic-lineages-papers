module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalOutputInductionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalOutputProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open OriginalLambdaTraversalSelection OriginalLambdaTraversalOutput OriginalLambdaTraversalOutputSyntaxProof
open OriginalLambdaTraversalOutputBindingProof
open InternalOriginalUniformDescentSelection (Data)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}
/-- The final right-payload witness is bound and eliminated inside the calculus. -/
theorem invariantAtInput (data : Data) (window : Program 1) (out input typ parameter : OrdinaryArithmetic.Term α)
    (hp : Nonempty (Derivation body Gamma (premises data window out input typ parameter))) :
    Nonempty (Derivation body Gamma (outputInvariant data window out input typ parameter)) := by
  apply programCases InternalUnpair.right (Fin.cons input Fin.elim0) _
  intro β j Delta payload hj hr
  rw [outputInvariantRename]
  simp only [consTermRename,emptyRename] at hr
  have hp' := renameInto hp j Delta hj
  rw [premisesRename] at hp'
  exact atPayloadApply data window payload (input.relabel j) (typ.relabel j)
    (out.relabel j) (parameter.relabel j)
    (OriginalLambdaTraversalOutputInductionProof.payloadInvariant data window payload) hr hp'

theorem actualOriginalLambdaTraversalOutputLaws :
    OriginalLambdaTraversalSelectionTargets.ActualOriginalLambdaTraversalOutputLaws := by
  intro data window body α Delta out input typ parameter
  obtain ⟨h⟩ := invariantAtInput (body := body)
    (Gamma := premises data window out input typ parameter :: Delta)
    data window out input typ parameter ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalOutputProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalOutputProof
#print axioms LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalOutputProof.actualOriginalLambdaTraversalOutputLaws
