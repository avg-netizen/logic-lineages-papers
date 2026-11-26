module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParametersLeafProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParametersFieldQueriesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalFoldUnaryProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParametersUnaryProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalParameters
open OriginalRawSyntaxTransportInternalParametersBindingProof OriginalRawSyntaxTransportInternalParametersSyntaxProof
open OriginalRawSyntaxTransportInternalParametersQueryProof OriginalRawSyntaxTransportInternalParametersFieldQueriesProof
open OriginalRawSyntaxTransportInternalMachineExpansionProof OriginalRawSyntaxTransportInternalFoldUnaryProof
open OriginalRawSyntaxTransportInternalConstructorBoundsProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem unaryParametersAt (rank : Bool) (raw out d k other otherK child childK otherChildK : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (BelowRaw (fold (selectedMode rank)) rank raw)))
    (hf : Nonempty (Derivation body Delta (UnaryFields raw k child childK)))
    (hk : Nonempty (Derivation body Delta (graph2 nextCutoff
      (if rank then otherChildK else childK) (if rank then otherK else k) raw)))
    (hs : Nonempty (Derivation body Delta (graph3 (fold (selectedMode rank)) out d k raw))) :
    Nonempty (Derivation body Delta
      (graph3 (fold (selectedMode rank)) out other (if rank then otherK else k) raw)) := by
  apply ternaryCases (fold (selectedMode rank)) d childK child _
  intro beta j Theta childOut hj hc
  simp only [graph3Rename,cutoffChoiceRename]
  have hi' := renameInto hi j Theta hj
  have hf' := renameInto hf j Theta hj
  have hk' := renameInto hk j Theta hj
  have hs' := renameInto hs j Theta hj
  rw [belowRawRename] at hi'
  rw [unaryFieldsRename] at hf'
  simp only [graph2Rename,cutoffChoiceRename] at hk'
  rw [graph3Rename] at hs'
  have hc' := belowRawApply (fold (selectedMode rank)) rank (raw.relabel j) (child.relabel j)
    childOut (d.relabel j) (childK.relabel j) (other.relabel j) (otherChildK.relabel j) hi'
    (unaryChildStrict (raw.relabel j) (child.relabel j) (andLeft hf') (andLeft (andRight hf'))) hc
  have hr := unaryForward (selectedMode rank) (d.relabel j) (k.relabel j) (raw.relabel j)
    (child.relabel j) (childK.relabel j) childOut (out.relabel j) hf' hc hs'
  exact unaryBackward (selectedMode rank) (other.relabel j) (if rank then otherK.relabel j else k.relabel j)
    (raw.relabel j) (child.relabel j) (if rank then otherChildK.relabel j else childK.relabel j)
    childOut (out.relabel j) (andIntro (andLeft hf') (andIntro (andLeft (andRight hf')) hk')) hc' hr

theorem unaryParameters (rank : Bool) (raw out d k other otherK : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (BelowRaw (fold (selectedMode rank)) rank raw)))
    (ha : Nonempty (Derivation body Delta (graph1 (arityOf (.projection 0)) (suc z) raw)))
    (hs : Nonempty (Derivation body Delta (graph3 (fold (selectedMode rank)) out d k raw))) :
    Nonempty (Derivation body Delta
      (graph3 (fold (selectedMode rank)) out other (if rank then otherK else k) raw)) := by
  apply unaryFieldCases raw k otherK _
  intro beta j Theta child childK otherChildK hj hf hk hother
  simp only [graph3Rename,cutoffChoiceRename]
  have hi' := renameInto hi j Theta hj
  have ha' := renameInto ha j Theta hj
  have hs' := renameInto hs j Theta hj
  rw [belowRawRename] at hi'
  simp only [graph1Rename,sucRelabel,zRelabel] at ha'
  rw [graph3Rename] at hs'
  have hchosen : Nonempty (Derivation body Theta (graph2 nextCutoff
      (if rank then otherChildK else childK) (if rank then otherK.relabel j else k.relabel j) (raw.relabel j))) := by
    cases rank with
    | false => exact hk
    | true => exact hother
  exact unaryParametersAt rank (raw.relabel j) (out.relabel j) (d.relabel j) (k.relabel j)
    (other.relabel j) (otherK.relabel j) child childK otherChildK hi' (andIntro ha' (andIntro hf hk)) hchosen hs'

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParametersUnaryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParametersUnaryProof
