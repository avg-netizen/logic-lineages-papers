module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParametersUnaryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalFoldBinaryProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParametersBinaryProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalParameters
open OriginalRawSyntaxTransportInternalParametersBindingProof OriginalRawSyntaxTransportInternalParametersSyntaxProof
open OriginalRawSyntaxTransportInternalParametersQueryProof OriginalRawSyntaxTransportInternalParametersFieldQueriesProof
open OriginalRawSyntaxTransportInternalMachineExpansionProof OriginalRawSyntaxTransportInternalFoldBinaryProof
open OriginalRawSyntaxTransportInternalConstructorBoundsProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem binaryParametersAt (rank : Bool) (raw out d k other otherK first second : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (BelowRaw (fold (selectedMode rank)) rank raw)))
    (hf : Nonempty (Derivation body Delta (BinaryFields raw first second)))
    (hs : Nonempty (Derivation body Delta (graph3 (fold (selectedMode rank)) out d k raw))) :
    Nonempty (Derivation body Delta
      (graph3 (fold (selectedMode rank)) out other (if rank then otherK else k) raw)) := by
  apply binaryChildCases (fold (selectedMode rank)) d k first second _
  intro beta j Theta firstOut secondOut hj hfirst hsecond
  simp only [graph3Rename,cutoffChoiceRename]
  have hi' := renameInto hi j Theta hj
  have hf' := renameInto hf j Theta hj
  have hs' := renameInto hs j Theta hj
  rw [belowRawRename] at hi'
  rw [binaryFieldsRename] at hf'
  rw [graph3Rename] at hs'
  have hb := binaryChildrenStrict (raw.relabel j) (first.relabel j) (second.relabel j)
    (andLeft hf') (andLeft (andRight hf')) (andRight (andRight hf'))
  have hfirst' := belowRawApply (fold (selectedMode rank)) rank (raw.relabel j) (first.relabel j)
    firstOut (d.relabel j) (k.relabel j) (other.relabel j) (otherK.relabel j) hi' (andLeft hb) hfirst
  have hsecond' := belowRawApply (fold (selectedMode rank)) rank (raw.relabel j) (second.relabel j)
    secondOut (d.relabel j) (k.relabel j) (other.relabel j) (otherK.relabel j) hi' (andRight hb) hsecond
  have hr := binaryForward (selectedMode rank) (d.relabel j) (k.relabel j) (raw.relabel j)
    (first.relabel j) (second.relabel j) firstOut secondOut (out.relabel j) hf' hfirst hsecond hs'
  exact binaryBackward (selectedMode rank) (other.relabel j) (if rank then otherK.relabel j else k.relabel j)
    (raw.relabel j) (first.relabel j) (second.relabel j) firstOut secondOut (out.relabel j)
    hf' hfirst' hsecond' hr

theorem binaryParameters (rank : Bool) (raw out d k other otherK : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (BelowRaw (fold (selectedMode rank)) rank raw)))
    (ha : Nonempty (Derivation body Delta (graph1 (arityOf (.projection 0)) (suc (suc z)) raw)))
    (hs : Nonempty (Derivation body Delta (graph3 (fold (selectedMode rank)) out d k raw))) :
    Nonempty (Derivation body Delta
      (graph3 (fold (selectedMode rank)) out other (if rank then otherK else k) raw)) := by
  apply binaryFieldCases raw _
  intro beta j Theta first second hj hf hsecond
  simp only [graph3Rename,cutoffChoiceRename]
  have hi' := renameInto hi j Theta hj
  have ha' := renameInto ha j Theta hj
  have hs' := renameInto hs j Theta hj
  rw [belowRawRename] at hi'
  simp only [graph1Rename,sucRelabel,zRelabel] at ha'
  rw [graph3Rename] at hs'
  exact binaryParametersAt rank (raw.relabel j) (out.relabel j) (d.relabel j) (k.relabel j)
    (other.relabel j) (otherK.relabel j) first second hi' (andIntro ha' (andIntro hf hsecond)) hs'

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParametersBinaryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParametersBinaryProof
