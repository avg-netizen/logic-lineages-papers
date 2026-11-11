module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalizedTypedTransportDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableObjectDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalizedObjectTypedTransport
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open UniformCertificateCompletion OriginalRawObjectTransport
open OriginalTransparentDecoderValidatorCollapse
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Actual original Object weakening followed by the unchanged canonical
Object Program. Its context/payload are recovered internally. The original
outer window is essential: outside it the old typed fallback is arbitrary. -/
def Weakening (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) : Prop :=
  let r := refined p H G W
  let f := OriginalLambdaTraversalSelection.finalInputs r
  let comp := GlobalSourcePackage.computability f
  let K := OriginalFinalVariableObject.canonicalObjectProgram r
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (context : Nat) (typ d input shifted out : OTerm alpha),
  Nonempty (Derivation body Delta
    ((graph1 f.window (numeral 1) (numeral context) ⊓
      (graph3 comp.typed (numeral 1) (numeral context) typ input ⊓
        (graph2 shiftObjectRaw shifted d input ⊓
          graph2 K out (numeral context) shifted))).imp
      (graph3 comp.typed (numeral 1) (numeral context) typ out)))

/-- Actual original Object erasure followed by that SAME canonical Object
Program. A genuine nonempty original context is required. No erased-type
window, transformed fixedness, canonicality, rank or payload premise is added. -/
def Erasure (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) : Prop :=
  let r := refined p H G W
  let f := OriginalLambdaTraversalSelection.finalInputs r
  let comp := GlobalSourcePackage.computability f
  let K := OriginalFinalVariableObject.canonicalObjectProgram r
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (context : Nat) (typ d gamma extended input erased out : OTerm alpha),
  Nonempty (Derivation body Delta
    ((graph1 f.window (numeral 1) (numeral context) ⊓
      (graph3 comp.typed (numeral 1) (numeral context) typ input ⊓
        (graph1 InternalUnpair.left extended input ⊓
          (graph2 InternalListCodec.consCode extended d gamma ⊓
            (graph1 eraseObjectRaw erased input ⊓
              graph2 K out (numeral context) erased))))).imp
      (graph3 comp.typed (numeral 1) (numeral context) typ out)))

/- These are SAME-final outer typed conclusions, not raw selectedTyped
transport, canonical coherence, cancellation, rank preservation, I or C.
The original K graph must supply the output's transition fixedness. -/
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalizedObjectTypedTransport
