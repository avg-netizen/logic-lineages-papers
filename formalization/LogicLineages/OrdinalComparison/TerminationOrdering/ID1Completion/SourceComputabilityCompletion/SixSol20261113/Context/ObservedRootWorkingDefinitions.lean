module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionStructuralTraversalDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedRootWorkingDefinitions
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

open OriginalAllPositionStructuralTraversalDefinitions

/-- Binary key observation retains the actual runtime parameter. -/
def observations {alpha : Type} (p : GlobalSourcePackage.Inputs)
    (H G : Program 1) (W : Program 2)
    (out input parameter mark : OTerm alpha) : Formula alpha :=
  (graph2 (OriginalStructuralClassKeyDefinitions.key p H G W) mark out parameter).iff
    (graph2 (OriginalStructuralClassKeyDefinitions.key p H G W) mark input parameter)

/-- Needed BEFORE payload induction: the actual selected OTHER leaf, including
all bounded-descent iterations and sidecar guards, preserves K. This is a
separate obligation, not a premise added to the full traversal target. -/
def OtherLeafLaw (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3) : Prop :=
  let r := refined p H G W P
  let D := OriginalLambdaTraversalSelection.leafData r.base r.window
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (out input typ parameter mark : OTerm alpha),
  Nonempty (Derivation body Delta
    ((OriginalFunctionNeutrality.windowGraph r.window input parameter ⊓
      (InternalParameterizedCanonicalResultFold.sourcePremises D input typ parameter ⊓
        (graph1 OriginalLambdaTraversalInternal.otherTag InternalOriginalStepGuard.one input ⊓
          graph2 (OriginalLambdaTraversalSelection.leaf r.base r.window) out input parameter))).imp
      (observations p H G W out input parameter mark)))

/-- Exact full new structural traversal, arbitrary original runtime parameter.
There are NO child congruence, key equality, leaf preservation, successful-run,
native calibration, fixedness or canonicality hypotheses. -/
def TraversalLaw (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3) : Prop :=
  let r := refined p H G W P
  let D := OriginalLambdaTraversalSelection.leafData r.base r.window
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (out input typ parameter mark : OTerm alpha),
  Nonempty (Derivation body Delta
    ((OriginalFunctionNeutrality.windowGraph r.window input parameter ⊓
      (InternalParameterizedCanonicalResultFold.sourcePremises D input typ parameter ⊓
        graph2 (OriginalLambdaTraversalSelection.canonical r.base r.window)
          out input parameter)).imp
      (observations p H G W out input parameter mark)))

/-- The actual unchanged final application-only fold at that identical r.
The original final source/window graphs remain the only domain hypotheses. -/
def FinalLaw (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3) : Prop :=
  let r := refined p H G W P
  let f := OriginalLambdaTraversalSelection.finalInputs r
  let D := OriginalLambdaTraversalSelection.finalData r
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (out input typ parameter mark : OTerm alpha),
  Nonempty (Derivation body Delta
    ((OriginalFunctionNeutrality.windowGraph f.window input parameter ⊓
      (InternalParameterizedCanonicalResultFold.sourcePremises D input typ parameter ⊓
        InternalParameterizedCanonicalResultFold.foldGraph D out input parameter)).imp
      (observations p H G W out input parameter mark)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedRootWorkingDefinitions
