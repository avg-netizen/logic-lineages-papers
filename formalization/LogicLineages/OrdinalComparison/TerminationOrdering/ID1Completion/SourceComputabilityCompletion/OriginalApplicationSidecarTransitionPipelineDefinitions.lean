module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarTransitionTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarTransitionPipelineDefinitions
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalOriginalUniformDescentSelection (Data)
open OriginalApplicationSidecar
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- A literal existing observer wrapper; this helper does not replace any Program. -/
def observed (active : Program 2) (mark : Program 1) (previous : Program 2) : Program 2 :=
  InternalAcceptance.branch active previous
    (InternalAcceptance.branch
      (InternalApplicationStepPeel.same
        (.composition mark (fun _ : Fin 1 => previous))
        (.composition mark (fun _ : Fin 1 => .projection 0)))
      (.projection 0) previous)
def neutral (data : Data) (window : Program 1) : Program 2 :=
  observed (OriginalFunctionNeutrality.active data window) OriginalFunctionNeutrality.mark
    (representative data window)
def shape (data : Data) (window : Program 1) : Program 2 :=
  observed (OriginalFunctionNeutrality.active data window) OriginalConstructorShape.mark (neutral data window)
def variableStage (data : Data) (window : Program 1) : Program 2 :=
  observed (OriginalFunctionNeutrality.active data window) OriginalVariableRepresentative.variableMark (shape data window)
def spine (data : Data) (window : Program 1) : Program 2 :=
  observed (OriginalFunctionNeutrality.active data window) BottomSpineMeasure.measure (variableStage data window)
def bottom (data : Data) (window : Program 1) : Program 2 :=
  observed (OriginalFunctionNeutrality.active data window) BottomRepresentative.bottomTest (spine data window)
def sourceHyp {alpha : Type} (data : Data) (window : Program 1)
    (input typ parameter : OrdinaryArithmetic.Term alpha) : Formula alpha :=
  OriginalFunctionNeutrality.windowGraph window input parameter ⊓
    InternalParameterizedCanonicalResultFold.sourcePremises (originalData data window) input typ parameter

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarTransitionPipelineDefinitions
