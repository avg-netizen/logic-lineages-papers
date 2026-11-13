module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionStructuralTraversalDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedClassDefinitions
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The original final source/window/fold premises at the SAME selected tuple. -/
def premises {alpha : Type} (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3) (out input typ parameter : OTerm alpha) : Formula alpha :=
  let r := OriginalAllPositionStructuralTraversalDefinitions.refined p H G W P
  let f := OriginalLambdaTraversalSelection.finalInputs r
  let D := OriginalLambdaTraversalSelection.finalData r
  OriginalFunctionNeutrality.windowGraph f.window input parameter ⊓
    (InternalParameterizedCanonicalResultFold.sourcePremises D input typ parameter ⊓
      InternalParameterizedCanonicalResultFold.foldGraph D out input parameter)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedClassDefinitions
