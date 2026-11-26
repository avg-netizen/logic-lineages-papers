module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalCancellationBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParametersQueryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalFoldOrdinaryProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalCancellationOrdinaryProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalCancellation
open OriginalRawSyntaxTransportInternalCancellationBindingProof OriginalRawSyntaxTransportInternalCancellationSyntaxProof
open OriginalRawSyntaxTransportInternalParametersQueryProof
open OriginalRawSyntaxTransportInternalFoldOrdinaryProof OriginalRawSyntaxTransportInternalFoldConstructorFieldsProof
open OriginalRawSyntaxTransportInternalConstructorBoundsProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem ordinaryRightInverseAt (raw shifted d k head child childOut : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (BelowRaw (fold .shift) (fold .erase) raw)))
    (hc : Nonempty (Derivation body Delta (graph2 ordinaryConstructor raw head child)))
    (hchild : Nonempty (Derivation body Delta (graph3 (fold .shift) childOut (numeral 0) (k) child)))
    (hs : Nonempty (Derivation body Delta (graph3 (fold .shift) shifted (numeral 0) k raw))) :
    Nonempty (Derivation body Delta (graph3 (fold .erase) raw d k shifted)) := by
  have hf := ordinaryFields raw k head child hc
  have hl := unaryChildStrict raw child (andLeft hf) (andLeft (andRight hf))
  have he := belowRawApply (fold .shift) (fold .erase) raw child d (k) childOut hi hl hchild
  have hshift := ordinaryForward .shift raw shifted (numeral 0) k head child childOut hc hchild hs
  exact ordinaryBackward .erase shifted raw d k head childOut child hshift he hc

theorem ordinaryRightInverse (raw shifted d k head child : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (BelowRaw (fold .shift) (fold .erase) raw)))
    (hc : Nonempty (Derivation body Delta (graph2 ordinaryConstructor raw head child)))
    (hs : Nonempty (Derivation body Delta (graph3 (fold .shift) shifted (numeral 0) k raw))) :
    Nonempty (Derivation body Delta (graph3 (fold .erase) raw d k shifted)) := by
  apply ternaryCases (fold .shift) (numeral 0) (k) child _
  intro beta j Theta childOut hj hchild
  rw [graph3Rename]
  have hi' := renameInto hi j Theta hj
  have hc' := renameInto hc j Theta hj
  have hs' := renameInto hs j Theta hj
  rw [belowRawRename] at hi'
  rw [graph2Rename] at hc'
  simp only [graph3Rename,numeral,zRelabel] at hs'
  simp only [numeral,zRelabel,sucRelabel] at hchild
  exact ordinaryRightInverseAt (raw.relabel j) (shifted.relabel j) (d.relabel j) (k.relabel j)
    (head.relabel j) (child.relabel j) childOut hi' hc' hchild hs'

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalCancellationOrdinaryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalCancellationOrdinaryProof
