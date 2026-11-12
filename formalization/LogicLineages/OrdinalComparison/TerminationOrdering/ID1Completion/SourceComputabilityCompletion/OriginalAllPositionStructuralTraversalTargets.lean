module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionStructuralTraversalDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionStructuralTraversalTargets
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open OriginalAllPositionStructuralTraversalDefinitions

/-- Exact actual traversal: only its source/window/run and the original cutoff range.
No constructor/OTHER supplier is assumed by this target. -/
def TraversalLaw (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3) : Prop :=
  let r := refined p H G W P
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (out input typ parameter mark cutoff : OTerm alpha),
  Nonempty (Derivation body Delta
    ((OriginalIndexedObserverDefinitions.premises r.base r.window out input typ parameter ⊓
      OriginalIndexedObserverDefinitions.ActualRange cutoff parameter).imp
      (OriginalIndexedObserverDefinitions.observations (observer p H G W)
        out input parameter mark cutoff)))

/-- Same tuple and unchanged actual final fold. No erased-source, key-hit,
canonical-fixedness or supplier hypothesis is added. -/
def FinalLaw (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3) : Prop :=
  let r := refined p H G W P
  let f := OriginalLambdaTraversalSelection.finalInputs r
  let D := OriginalLambdaTraversalSelection.finalData r
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (out input typ parameter mark cutoff : OTerm alpha),
  Nonempty (Derivation body Delta
    (((OriginalFunctionNeutrality.windowGraph f.window input parameter ⊓
      (InternalParameterizedCanonicalResultFold.sourcePremises D input typ parameter ⊓
        InternalParameterizedCanonicalResultFold.foldGraph D out input parameter)) ⊓
      OriginalIndexedObserverDefinitions.ActualRange cutoff parameter).imp
      (OriginalIndexedObserverDefinitions.observations (observer p H G W)
        out input parameter mark cutoff)))

def ActualTraversal : Prop :=
  ∀ p H G W P, TraversalLaw p H G W P

def ActualFinal : Prop :=
  ∀ p H G W P, FinalLaw p H G W P

/- These are specifications, not completed proofs of either whole-fold law. -/

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionStructuralTraversalTargets
