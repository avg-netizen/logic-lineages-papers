module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRankGuardedLeafDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableObjectDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalGuardedRank
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Exactly the guarded initial tuple, transparent decoding, and ONE variable
refinement used by the accepted previous Package and the actual OTHER leaf. -/
abbrev refined := OriginalRankGuardedLeaf.refined

/-- Actual all-variable-occurrence rank preservation by the lambda/application
traversal C. Its leafData, window and runtime parameter are unchanged. This is
an independent internal derivation, not an instance of native calibration. -/
def TraversalRankLaw (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) : Prop :=
  let r := refined p H G W
  OriginalLambdaTraversalSelection.PreservesObserver r.base r.window
    OriginalRawSyntaxTransport.variableRankPackedRaw

/-- Rank invariance of the SAME unchanged final canonical fold. Original
window and final source/type graphs are the only input conditions; the fold
graph supplies its actual output. No rank or canonicality premise is added. -/
def FinalRankLaw (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) : Prop :=
  let r := refined p H G W
  let f := OriginalLambdaTraversalSelection.finalInputs r
  let D := OriginalLambdaTraversalSelection.finalData r
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (out input typ parameter rank : OTerm alpha),
  Nonempty (Derivation body Delta
    ((OriginalFunctionNeutrality.windowGraph f.window input parameter ⊓
      (InternalParameterizedCanonicalResultFold.sourcePremises D input typ parameter ⊓
        InternalParameterizedCanonicalResultFold.foldGraph D out input parameter)).imp
      ((graph1 OriginalRawSyntaxTransport.variableRankPackedRaw rank out).iff
        (graph1 OriginalRawSyntaxTransport.variableRankPackedRaw rank input))))

/-- The actual canonical Object wrapper K at this SAME r and final D preserves
all variable occurrences. The active original outer window is explicit; input
coordinates and final selected source/type are recovered internally from the
original Outer typed graph. No raw selectedTyped transport is assumed. -/
def ObjectRankLaw (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) : Prop :=
  let r := refined p H G W
  let f := OriginalLambdaTraversalSelection.finalInputs r
  let comp := GlobalSourcePackage.computability f
  let K := OriginalFinalVariableObject.canonicalObjectProgram r
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (context : Nat) (out input typ rank : OTerm alpha),
  Nonempty (Derivation body Delta
    ((graph1 f.window (numeral 1) (numeral context) ⊓
      (graph3 comp.typed (numeral 1) (numeral context) typ input ⊓
        graph2 K out (numeral context) input)).imp
      ((graph1 OriginalRawObjectTransport.variableRankObjectRaw rank out).iff
        (graph1 OriginalRawObjectTransport.variableRankObjectRaw rank input))))

/-- Retain the ENTIRE accepted representative Properties, hence its complete
prior Package, at one original globally selected tuple with these three new
internal laws at the exact same once-refined final pipeline. -/
def Properties (n : Nat) (arity : Fin n → Nat)
    (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) : Prop :=
  OriginalRankGuardedRepresentative.Properties n arity p H G W ∧
    TraversalRankLaw p H G W ∧ FinalRankLaw p H G W ∧ ObjectRankLaw p H G W

/- SPECIFICATION ONLY. No canonical cancellation, positive-path transport,
substitution, I/C or all-term accessibility is asserted by these contracts. -/
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalGuardedRank
