module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalCancellationBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParametersQueryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalFoldLambdaProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalCancellationLambdaProof
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
open OriginalRawSyntaxTransportInternalFoldLambdaProof OriginalRawSyntaxTransportInternalFoldConstructorFieldsProof
open OriginalRawSyntaxTransportInternalConstructorBoundsProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem lambdaRightInverseAt (raw shifted d k domain child childOut : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (BelowRaw (fold .shift) (fold .erase) raw)))
    (hc : Nonempty (Derivation body Delta (graph2 lambdaConstructor raw domain child)))
    (hchild : Nonempty (Derivation body Delta (graph3 (fold .shift) childOut (numeral 0) (suc k) child)))
    (hs : Nonempty (Derivation body Delta (graph3 (fold .shift) shifted (numeral 0) k raw))) :
    Nonempty (Derivation body Delta (graph3 (fold .erase) raw d k shifted)) := by
  have hf := lambdaFields raw k domain child hc
  have hl := unaryChildStrict raw child (andLeft hf) (andLeft (andRight hf))
  have he := belowRawApply (fold .shift) (fold .erase) raw child d (suc k) childOut hi hl hchild
  have hshift := lambdaForward .shift raw shifted (numeral 0) k domain child childOut hc hchild hs
  exact lambdaBackward .erase shifted raw d k domain childOut child hshift he hc

theorem lambdaRightInverse (raw shifted d k domain child : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (BelowRaw (fold .shift) (fold .erase) raw)))
    (hc : Nonempty (Derivation body Delta (graph2 lambdaConstructor raw domain child)))
    (hs : Nonempty (Derivation body Delta (graph3 (fold .shift) shifted (numeral 0) k raw))) :
    Nonempty (Derivation body Delta (graph3 (fold .erase) raw d k shifted)) := by
  apply ternaryCases (fold .shift) (numeral 0) (suc k) child _
  intro beta j Theta childOut hj hchild
  rw [graph3Rename]
  have hi' := renameInto hi j Theta hj
  have hc' := renameInto hc j Theta hj
  have hs' := renameInto hs j Theta hj
  rw [belowRawRename] at hi'
  rw [graph2Rename] at hc'
  simp only [graph3Rename,numeral,zRelabel] at hs'
  simp only [numeral,zRelabel,sucRelabel] at hchild
  exact lambdaRightInverseAt (raw.relabel j) (shifted.relabel j) (d.relabel j) (k.relabel j)
    (domain.relabel j) (child.relabel j) childOut hi' hc' hchild hs'

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalCancellationLambdaProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalCancellationLambdaProof
