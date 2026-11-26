module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalOutputLambdaOpeningProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalOutputProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalLambdaOutputProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalLambdaObserverProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalObserverSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalObserverLambdaInductionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalOriginalUniformDescentSelection (Data)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open OriginalLambdaTraversalSelection OriginalLambdaTraversalObserver
open OriginalLambdaTraversalObserverSyntaxProof
open OriginalLambdaTraversalInternal OriginalLambdaTraversalInternalFieldsSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- The actual child traversal has its own original extended parameter. Its
checked output laws reconstruct the parent lambda fields, so all five original
observers follow from literal tag ONE without an observer IH or new premise. -/
theorem atOutput (data : Data) (window : Program 1)
    (input typ out parameter mark d e child bodyParameter childOut : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (premises data window out input typ parameter)))
    (hf : Nonempty (Derivation body Delta (LambdaFields input d e child parameter bodyParameter)))
    (hchild : Nonempty (Derivation body Delta
      (graph2 (canonical data window) childOut child bodyParameter))) :
    Nonempty (Derivation body Delta (observations out input mark)) := by
  have hs := andLeft (andRight hp)
  have childPremises := OriginalLambdaTraversalLambdaOutputProof.childPremises data window
    input d e child typ parameter bodyParameter hf (andLeft hp) hs
  have childInvariant := OriginalLambdaTraversalOutputProof.invariantAtInput data window
    childOut child e bodyParameter
    (andIntro (andLeft childPremises) (andIntro (andRight childPremises) hchild))
  have constructor := OriginalLambdaTraversalInternalLambdaProof.lambdaForward (leaf data window)
    input d e child parameter bodyParameter childOut out hf hchild (andRight (andRight hp))
  have rebuilt := OriginalLambdaTraversalLambdaRebuildProof.sourceRebuild data window
    input out d e child childOut typ parameter bodyParameter hf (andRight hs) (andLeft hs)
    (andLeft childInvariant) (andLeft (andRight childInvariant)) constructor
  exact OriginalLambdaTraversalLambdaObserverProof.atTags out input mark
    (andLeft (andLeft (andRight rebuilt))) (andLeft hf)

/-- Bind and discharge the actual child C output inside the calculus. The
different child parameter is the traversal's literal childParameter graph. -/
theorem atFields (data : Data) (window : Program 1)
    (input typ out parameter mark d e child bodyParameter : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (premises data window out input typ parameter)))
    (hf : Nonempty (Derivation body Delta (LambdaFields input d e child parameter bodyParameter))) :
    Nonempty (Derivation body Delta (observations out input mark)) := by
  apply programCases (canonical data window) (Fin.cons child (Fin.cons bodyParameter Fin.elim0)) _
  intro beta j Theta childOut hj hchild
  rw [observationsRename]
  simp only [consTermRename,emptyRename] at hchild
  have hp' := renameInto hp j Theta hj
  rw [premisesRename] at hp'
  have hf' := renameInto hf j Theta hj
  rw [lambdaFieldsRename] at hf'
  exact atOutput data window (input.relabel j) (typ.relabel j) (out.relabel j)
    (parameter.relabel j) (mark.relabel j) (d.relabel j) (e.relabel j) (child.relabel j)
    (bodyParameter.relabel j) childOut hp' hf' hchild

/-- The lambda case of the joint observer induction uses only the original
window/source/type/C premises and the actual raw tag; selectors, child output
and the constructor graph are supplied internally by their checked laws. -/
theorem atTag (data : Data) (window : Program 1)
    (input typ out parameter mark : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (premises data window out input typ parameter)))
    (ht : Nonempty (Derivation body Delta
      (graph1 OriginalLambdaTraversal.rawTag InternalOriginalStepGuard.one input))) :
    Nonempty (Derivation body Delta (observations out input mark)) := by
  apply OriginalLambdaTraversalOutputLambdaOpeningProof.lambdaFieldsCases input parameter _ ht
  intro beta j Theta d e child bodyParameter hj hf
  rw [observationsRename]
  have hp' := renameInto hp j Theta hj
  rw [premisesRename] at hp'
  exact atFields data window (input.relabel j) (typ.relabel j) (out.relabel j)
    (parameter.relabel j) (mark.relabel j) d e child bodyParameter hp' hf

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalObserverLambdaInductionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalObserverLambdaInductionProof
