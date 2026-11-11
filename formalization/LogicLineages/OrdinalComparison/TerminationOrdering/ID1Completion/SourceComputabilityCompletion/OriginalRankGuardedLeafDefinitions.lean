module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRankGuardedRepresentativeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRankGuardedLeaf
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors (graph1 graph2)
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Exactly the accepted initial rank guard, transparent decoder selection,
and ONE variable refinement. No later representative is replaced. -/
def refined (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) :
    GlobalSourcePackage.Inputs :=
  OriginalVariableLeaves.refineInputs G
    (OriginalRankGuardedRepresentative.transparentInputs H G W p)

/-- The actual prior selection used inside the unchanged application sidecar.
This supplier precedes the eventual selected leaf and is not finalData. -/
def priorData (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) :
    InternalOriginalUniformDescentSelection.Data :=
  let r := refined p H G W
  OriginalApplicationSidecar.originalData
    (OriginalLambdaTraversalSelection.transparentData r.base) r.window

/-- Internal rank preservation by the real prior bounded-descent leaf.
All tags are allowed here; each guard returns the old candidate or the raw
input. Actual iteration and validity at intermediate values are obligations. -/
def PriorRankLaw (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (out input parameter rank : OTerm alpha),
  let r := refined p H G W
  let D := priorData p H G W
  Nonempty (Derivation body Delta
    ((OriginalFunctionNeutrality.windowGraph r.window input parameter ⊓
      (graph2 (InternalOriginalUniformDescentSelection.validity D)
        InternalOriginalStepGuard.one input parameter ⊓
        graph2 (InternalParameterizedCanonicalResultFold.leaf D) out input parameter)).imp
      ((graph1 OriginalRawSyntaxTransport.variableRankPackedRaw rank out).iff
        (graph1 OriginalRawSyntaxTransport.variableRankPackedRaw rank input))))

/-- The ACTUAL selected leaf, exactly at the OTHER-tag inputs where the
accepted application/lambda traversal invokes it. Window, original source
validity, original outer type and literal otherTag acceptance are premises.
No output-rank, intermediate invariant, successful decode, calibration or
replacement-leaf assumption is present. -/
def OtherRankLaw (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (out input typ parameter rank : OTerm alpha),
  let r := refined p H G W
  let D := OriginalLambdaTraversalSelection.leafData r.base r.window
  Nonempty (Derivation body Delta
    ((OriginalFunctionNeutrality.windowGraph r.window input parameter ⊓
      (InternalParameterizedCanonicalResultFold.sourcePremises D input typ parameter ⊓
        (graph1 OriginalLambdaTraversalInternal.otherTag InternalOriginalStepGuard.one input ⊓
          graph2 (OriginalLambdaTraversalSelection.leaf r.base r.window) out input parameter))).imp
      ((graph1 OriginalRawSyntaxTransport.variableRankPackedRaw rank out).iff
        (graph1 OriginalRawSyntaxTransport.variableRankPackedRaw rank input))))

/- SPECIFICATION ONLY. This is not full C or final-fold rank invariance,
canonical cancellation, substitution/I/C, or closed accessibility. Every
Program tuple remains arbitrary; native calibration cannot discharge either
internal Derivation contract. -/
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRankGuardedLeaf
