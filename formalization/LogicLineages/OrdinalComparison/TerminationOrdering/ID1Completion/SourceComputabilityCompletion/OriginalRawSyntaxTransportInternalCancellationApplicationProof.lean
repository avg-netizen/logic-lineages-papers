module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalCancellationBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParametersQueryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalFoldApplicationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalCancellationApplicationProof
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
open OriginalRawSyntaxTransportInternalFoldApplicationProof OriginalRawSyntaxTransportInternalFoldConstructorFieldsProof
open OriginalRawSyntaxTransportInternalConstructorBoundsProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem applicationRightInverseAt (raw shifted d k domain first second firstOut secondOut : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (BelowRaw (fold .shift) (fold .erase) raw)))
    (hc : Nonempty (Derivation body Delta (graph3 applicationConstructor raw domain first second)))
    (hfirst : Nonempty (Derivation body Delta (graph3 (fold .shift) firstOut (numeral 0) k first)))
    (hsecond : Nonempty (Derivation body Delta (graph3 (fold .shift) secondOut (numeral 0) k second)))
    (hs : Nonempty (Derivation body Delta (graph3 (fold .shift) shifted (numeral 0) k raw))) :
    Nonempty (Derivation body Delta (graph3 (fold .erase) raw d k shifted)) := by
  have hf := applicationFields raw domain first second hc
  have hl := binaryChildrenStrict raw first second (andLeft hf) (andLeft (andRight hf)) (andRight (andRight hf))
  have heFirst := belowRawApply (fold .shift) (fold .erase) raw first d k firstOut hi (andLeft hl) hfirst
  have heSecond := belowRawApply (fold .shift) (fold .erase) raw second d k secondOut hi (andRight hl) hsecond
  have hshift := applicationForward .shift raw shifted (numeral 0) k domain first second firstOut secondOut hc hfirst hsecond hs
  exact applicationBackward .erase shifted raw d k domain firstOut secondOut first second hshift heFirst heSecond hc

theorem applicationRightInverse (raw shifted d k domain first second : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (BelowRaw (fold .shift) (fold .erase) raw)))
    (hc : Nonempty (Derivation body Delta (graph3 applicationConstructor raw domain first second)))
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
  exact applicationRightInverseAt (raw.relabel j) (shifted.relabel j) (d.relabel j) (k.relabel j)
    (domain.relabel j) (first.relabel j) (second.relabel j) firstOut secondOut hi' hc' hfirst hsecond hs'

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalCancellationApplicationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalCancellationApplicationProof
