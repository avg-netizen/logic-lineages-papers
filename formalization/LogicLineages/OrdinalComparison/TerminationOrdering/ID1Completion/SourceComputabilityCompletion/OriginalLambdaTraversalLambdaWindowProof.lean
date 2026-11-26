module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalLambdaSelectorProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalSelectionDefinitions
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalLambdaWindowProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open OriginalLambdaConstructorGraphSyntaxProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof InternalAcceptanceSupportProof
open OriginalLambdaTraversalLambdaSelectorProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Every window output is preserved at the actual lambda child parameter.
Only the outer context is observed; no decoding or closure premise is added. -/
theorem windowChild (window : Program 1) (value raw child parameter bodyParameter : OTerm alpha)
    (hp : Nonempty (Derivation body Delta
      (graph2 OriginalLambdaTraversal.childParameter bodyParameter raw parameter)))
    (hw : Nonempty (Derivation body Delta
      (graph2 (BottomRepresentative.windowAt window) value raw parameter))) :
    Nonempty (Derivation body Delta
      (graph2 (BottomRepresentative.windowAt window) value child bodyParameter)) := by
  apply programCases InternalUnpair.left (Fin.cons parameter Fin.elim0) _
  intro beta j Theta context hj hc
  rw [graph2Rename]
  simp only [consTermRename,emptyRename] at hc
  have hp' := renameInto hp j Theta hj
  have hw' := renameInto hw j Theta hj
  rw [graph2Rename] at hp' hw'
  let xx : Fin 2 → OTerm beta := Fin.cons (raw.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0)
  let yy : Fin 2 → OTerm beta := Fin.cons (child.relabel j) (Fin.cons (bodyParameter.relabel j) Fin.elim0)
  have hchild := childContext (raw.relabel j) (parameter.relabel j) (bodyParameter.relabel j) context hp' hc
  have hx := unaryValue InternalUnpair.left (.projection 1) context (parameter.relabel j) xx hc
    (projectionValue 1 xx)
  have hy := unaryValue InternalUnpair.left (.projection 1) context (bodyParameter.relabel j) yy hchild
    (projectionValue 1 yy)
  exact unaryValue window (leftOf (.projection 1)) (value.relabel j) context yy
    (unaryRecover window (leftOf (.projection 1)) (value.relabel j) context xx hw' hx) hy

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalLambdaWindowProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalLambdaWindowProof
