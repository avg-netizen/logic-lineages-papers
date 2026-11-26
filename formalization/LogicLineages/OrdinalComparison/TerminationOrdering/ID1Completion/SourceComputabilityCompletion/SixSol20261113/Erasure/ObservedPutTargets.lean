module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.PutIntegrationTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionStructuralTraversalRetentionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPositionStructuralKeyOpeningDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ObservedPut
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors UniformCertificateCompletion
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Preserve literal PUT before the original mixed preparation. -/
def prepared (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) :=
  OriginalMixedPrepared.prepared (PutIntegration.seed p H G W) H G W
/-- NEW tuple: accepted structural pre-key plus all-position observer OUTSIDE
active kernel, the accepted observed minimum and rank refinement. This is not
PutIntegration.finalData and asserts no equality to that older Data. -/
def refined (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3) :=
  OriginalAllPositionStructuralTraversalDefinitions.refined (prepared p H G W) H G W P
def finalInputs (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3) :=
  OriginalLambdaTraversalSelection.finalInputs (refined p H G W P)
def finalData (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3) :=
  OriginalLambdaTraversalSelection.finalData (refined p H G W P)
def key (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) :=
  OriginalStructuralClassKeyDefinitions.key (prepared p H G W) H G W

def ActualRetention : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (p : GlobalSourcePackage.Inputs)
    (H G : Program 1) (W : Program 2) (P : Program 3),
  GlobalSourcePackage.InputsCalibrated n arity p →
  OriginalTypedDecoder.HeadSignatureCalibrated n arity H →
  OriginalVariableLeaves.ContextGuardCalibrated n G →
  OriginalUniverseDecoder.HeadWindowCalibrated n arity W →
  OriginalTransparentMinimum.ClassTestCalibrated n arity P →
  OriginalMixedPrepared.Properties n arity (PutIntegration.seed p H G W) H G W P ∧
    OriginalAllPositionStructuralTraversalRetentionTargets.Retained n arity (prepared p H G W) H G W P

/-- Actual final guarded PUT at the NEW observer-aware Data, not a transported
claim obtained by silently identifying it with the older Data. -/
def ActualFinalPutStep : Prop :=
  ∀ (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (s t cert parameter typ raw head base label : OTerm alpha),
  Nonempty (Derivation body Delta
    ((graph2 (InternalOriginalUniformDescentSelection.validity (finalData p H G W P))
      (numeral 1) s parameter ⊓
      (graph2 InternalPairing.pairing s typ raw ⊓
      (graph2 OriginalRawSyntaxTransport.ordinaryConstructor raw head base ⊓
      (graph2 SixSol20261112.Erasure.PutRoot.resultCode t s label ⊓
       graph2 SixSol20261112.Erasure.PutRoot.certificateCode cert s label)))).imp
      (stepAccepted (finalData p H G W P) (finalInputs p H G W P).oldStep s t cert parameter)))

/-- Actual erased packed endpoints of one complete final fold preserve the
pre-minimum structural KEY and raw rank. Original lookup/delete/range graphs
retain the real context deletion; no desired observer/key/fixedness fact is an
input. This is not equality of final folded endpoints or Object cancellation. -/
def ActualFinalErasedObservations : Prop :=
  ∀ (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (input out typ parameter newParam context extended gamma d cutoff erasedInput erasedOut keyValue rank : OTerm alpha),
  Nonempty (Derivation body Delta
    (((OriginalFunctionNeutrality.windowGraph (finalInputs p H G W P).window input parameter ⊓
      (InternalParameterizedCanonicalResultFold.sourcePremises (finalData p H G W P) input typ parameter ⊓
        InternalParameterizedCanonicalResultFold.foldGraph (finalData p H G W P) out input parameter)) ⊓
      (OriginalIndexedObserverDefinitions.ActualRange cutoff parameter ⊓
      (graph2 InternalPairing.pairing parameter context extended ⊓
      (graph2 InternalPairing.pairing newParam context gamma ⊓
      (graph2 InternalRawListRecursion.lookup d cutoff extended ⊓
      (graph2 OriginalClassContextAllPositionObserver.deleteAt gamma cutoff extended ⊓
      (graph3 OriginalRawSyntaxTransport.erasePackedRaw erasedInput d cutoff input ⊓
        graph3 OriginalRawSyntaxTransport.erasePackedRaw erasedOut d cutoff out))))))).imp
      (((graph2 (key p H G W) keyValue erasedInput newParam).iff
        (graph2 (key p H G W) keyValue erasedOut newParam)) ⊓
        ((graph1 OriginalRawSyntaxTransport.variableRankPackedRaw rank erasedInput).iff
          (graph1 OriginalRawSyntaxTransport.variableRankPackedRaw rank erasedOut)))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ObservedPut
