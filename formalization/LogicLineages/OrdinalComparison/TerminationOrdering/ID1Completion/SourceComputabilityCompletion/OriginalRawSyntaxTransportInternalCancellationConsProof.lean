module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalCancellationBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParametersQueryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalFoldConsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalCancellationConsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z zRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalCancellation
open OriginalRawSyntaxTransportInternalCancellationBindingProof OriginalRawSyntaxTransportInternalCancellationSyntaxProof
open OriginalRawSyntaxTransportInternalParametersQueryProof
open OriginalRawSyntaxTransportInternalFoldConsProof OriginalRawSyntaxTransportInternalFoldConstructorFieldsProof
open OriginalRawSyntaxTransportInternalConstructorBoundsProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem consRightInverseAt (raw shifted d k tau first second firstOut secondOut : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (BelowRaw (fold .shift) (fold .erase) raw)))
    (hc : Nonempty (Derivation body Delta (graph3 consConstructor raw tau first second)))
    (hfirst : Nonempty (Derivation body Delta (graph3 (fold .shift) firstOut (numeral 0) k first)))
    (hsecond : Nonempty (Derivation body Delta (graph3 (fold .shift) secondOut (numeral 0) k second)))
    (hs : Nonempty (Derivation body Delta (graph3 (fold .shift) shifted (numeral 0) k raw))) :
    Nonempty (Derivation body Delta (graph3 (fold .erase) raw d k shifted)) := by
  have hf := consFields raw tau first second hc
  have hl := binaryChildrenStrict raw first second (andLeft hf) (andLeft (andRight hf)) (andRight (andRight hf))
  have heFirst := belowRawApply (fold .shift) (fold .erase) raw first d k firstOut hi (andLeft hl) hfirst
  have heSecond := belowRawApply (fold .shift) (fold .erase) raw second d k secondOut hi (andRight hl) hsecond
  have hshift := consForward .shift raw shifted (numeral 0) k tau first second firstOut secondOut hc hfirst hsecond hs
  exact consBackward .erase shifted raw d k tau firstOut secondOut first second hshift heFirst heSecond hc

theorem consRightInverse (raw shifted d k tau first second : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (BelowRaw (fold .shift) (fold .erase) raw)))
    (hc : Nonempty (Derivation body Delta (graph3 consConstructor raw tau first second)))
    (hs : Nonempty (Derivation body Delta (graph3 (fold .shift) shifted (numeral 0) k raw))) :
    Nonempty (Derivation body Delta (graph3 (fold .erase) raw d k shifted)) := by
  apply binaryChildCases (fold .shift) (numeral 0) k first second _
  intro beta j Theta firstOut secondOut hj hfirst hsecond
  rw [graph3Rename]
  have hi' := renameInto hi j Theta hj
  have hc' := renameInto hc j Theta hj
  have hs' := renameInto hs j Theta hj
  rw [belowRawRename] at hi'
  rw [graph3Rename] at hc'
  simp only [graph3Rename,numeral,zRelabel] at hs'
  simp only [numeral,zRelabel] at hfirst hsecond
  exact consRightInverseAt (raw.relabel j) (shifted.relabel j) (d.relabel j) (k.relabel j)
    (tau.relabel j) (first.relabel j) (second.relabel j) firstOut secondOut hi' hc' hfirst hsecond hs'

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalCancellationConsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalCancellationConsProof
