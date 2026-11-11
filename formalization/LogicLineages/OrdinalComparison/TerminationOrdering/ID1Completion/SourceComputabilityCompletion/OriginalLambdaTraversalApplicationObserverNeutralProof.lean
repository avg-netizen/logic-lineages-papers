module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFunctionNeutralityApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFunctionNeutralityDefinitions
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalApplicationObserverNeutralProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof (refl)
open OriginalFunctionNeutralityApplicationValuesProof OriginalFunctionNeutralityApplicationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- The actual parent neutrality test depends only on its function's original
root tag. A shared original root mark transfers that tag without assuming
that either function is non-lambda. -/
theorem atRootMark (d e fn arg fnOut argOut input out functionMark mark : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (graph4 application input d e fn arg)))
    (ho : Nonempty (Derivation body Delta (graph4 application out d e fnOut argOut)))
    (hfi : Nonempty (Derivation body Delta (graph1 OriginalConstructorShape.mark functionMark fn)))
    (hfo : Nonempty (Derivation body Delta (graph1 OriginalConstructorShape.mark functionMark fnOut))) :
    Nonempty (Derivation body Delta
      ((graph1 OriginalFunctionNeutrality.mark mark out).iff (graph1 OriginalFunctionNeutrality.mark mark input))) := by
  apply programCases OriginalConstructorShape.tag (Fin.cons fn Fin.elim0) _
  intro beta j Theta tag hj ht
  change Nonempty (Derivation body Theta
    (((graph1 OriginalNeutralLeaf.neutralTest mark out).iff (graph1 OriginalNeutralLeaf.neutralTest mark input)).relabel j))
  rw [neutralIffRename]
  simp only [consTermRename,emptyRename] at ht
  have hi' := renameInto hi j Theta hj
  have ho' := renameInto ho j Theta hj
  have hfi' := renameInto hfi j Theta hj
  have hfo' := renameInto hfo j Theta hj
  rw [graph4Rename] at hi' ho'
  rw [graph1Rename] at hfi' hfo'
  have htag := OriginalConstructorShapeRootFieldsProof.sharedTag (functionMark.relabel j)
    (fn.relabel j) (fnOut.relabel j) tag hfi' hfo' ht
  apply formulaCases (eqn tag (suc z))
  · let P := eqn tag (suc z)
    have he : Nonempty (Derivation body (P :: Theta) P) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact BottomRepresentativeInternalProof.indicatorIff OriginalNeutralLeaf.neutralTest
      (mark.relabel j) (out.relabel j) (input.relabel j) z z
      (neutralAtLambda (d.relabel j) (e.relabel j) (fnOut.relabel j) (argOut.relabel j)
        (out.relabel j) tag (withHyp ho' P) (withHyp htag P) he)
      (neutralAtLambda (d.relabel j) (e.relabel j) (fn.relabel j) (arg.relabel j)
        (input.relabel j) tag (withHyp hi' P) (withHyp ht P) he) ⟨refl z⟩
  · let P := (eqn tag (suc z)).not
    have he : Nonempty (Derivation body (P :: Theta) P) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact BottomRepresentativeInternalProof.indicatorIff OriginalNeutralLeaf.neutralTest
      (mark.relabel j) (out.relabel j) (input.relabel j) (suc z) (suc z)
      (neutralAtNonlambda (d.relabel j) (e.relabel j) (fnOut.relabel j) (argOut.relabel j)
        (out.relabel j) tag (withHyp ho' P) (withHyp htag P) he)
      (neutralAtNonlambda (d.relabel j) (e.relabel j) (fn.relabel j) (arg.relabel j)
        (input.relabel j) tag (withHyp hi' P) (withHyp ht P) he) ⟨refl (suc z)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalApplicationObserverNeutralProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalApplicationObserverNeutralProof
