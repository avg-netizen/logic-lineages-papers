module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalCancellationLambdaProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalCancellationOrdinaryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalCancellationApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalCancellationConsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalCancellationNumberedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserUnaryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserBinaryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserNumberedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalCancellationTagsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (zRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalCancellation
open OriginalRawSyntaxTransportInternalCancellationSyntaxProof
open OriginalRawSyntaxTransportInternalCancellationLambdaProof OriginalRawSyntaxTransportInternalCancellationOrdinaryProof
open OriginalRawSyntaxTransportInternalCancellationApplicationProof OriginalRawSyntaxTransportInternalCancellationConsProof
open OriginalRawSyntaxTransportInternalCancellationNumberedProof
open OriginalRawSyntaxTransportInternalParserUnaryProof OriginalRawSyntaxTransportInternalParserBinaryProof
open OriginalRawSyntaxTransportInternalParserNumberedProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem lambdaTagRightInverse (raw shifted d k : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (BelowRaw (fold .shift) (fold .erase) raw)))
    (ht : Nonempty (Derivation body Delta (graph1 rawTag (numeral 1) raw)))
    (hs : Nonempty (Derivation body Delta (graph3 (fold .shift) shifted (numeral 0) k raw))) :
    Nonempty (Derivation body Delta (graph3 (fold .erase) raw d k shifted)) := by
  apply lambdaCases raw _ ht
  intro beta j Theta domain child hj hc
  rw [graph3Rename]
  have hi' := renameInto hi j Theta hj
  have hs' := renameInto hs j Theta hj
  rw [belowRawRename] at hi'
  simp only [graph3Rename,numeral,zRelabel] at hs'
  exact lambdaRightInverse (raw.relabel j) (shifted.relabel j) (d.relabel j) (k.relabel j)
    domain child hi' hc hs'

theorem ordinaryTagRightInverse (raw shifted d k : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (BelowRaw (fold .shift) (fold .erase) raw)))
    (ht : Nonempty (Derivation body Delta (graph1 rawTag (numeral 4) raw)))
    (hs : Nonempty (Derivation body Delta (graph3 (fold .shift) shifted (numeral 0) k raw))) :
    Nonempty (Derivation body Delta (graph3 (fold .erase) raw d k shifted)) := by
  apply ordinaryCases raw _ ht
  intro beta j Theta head child hj hc
  rw [graph3Rename]
  have hi' := renameInto hi j Theta hj
  have hs' := renameInto hs j Theta hj
  rw [belowRawRename] at hi'
  simp only [graph3Rename,numeral,zRelabel] at hs'
  exact ordinaryRightInverse (raw.relabel j) (shifted.relabel j) (d.relabel j) (k.relabel j)
    head child hi' hc hs'

theorem applicationTagRightInverse (raw shifted d k : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (BelowRaw (fold .shift) (fold .erase) raw)))
    (ht : Nonempty (Derivation body Delta (graph1 rawTag (numeral 2) raw)))
    (hs : Nonempty (Derivation body Delta (graph3 (fold .shift) shifted (numeral 0) k raw))) :
    Nonempty (Derivation body Delta (graph3 (fold .erase) raw d k shifted)) := by
  apply applicationCases raw _ ht
  intro beta j Theta domain first second hj hc
  rw [graph3Rename]
  have hi' := renameInto hi j Theta hj
  have hs' := renameInto hs j Theta hj
  rw [belowRawRename] at hi'
  simp only [graph3Rename,numeral,zRelabel] at hs'
  exact applicationRightInverse (raw.relabel j) (shifted.relabel j) (d.relabel j) (k.relabel j)
    domain first second hi' hc hs'

theorem consTagRightInverse (raw shifted d k : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (BelowRaw (fold .shift) (fold .erase) raw)))
    (ht : Nonempty (Derivation body Delta (graph1 rawTag (numeral 7) raw)))
    (hs : Nonempty (Derivation body Delta (graph3 (fold .shift) shifted (numeral 0) k raw))) :
    Nonempty (Derivation body Delta (graph3 (fold .erase) raw d k shifted)) := by
  apply consCases raw _ ht
  intro beta j Theta tau first second hj hc
  rw [graph3Rename]
  have hi' := renameInto hi j Theta hj
  have hs' := renameInto hs j Theta hj
  rw [belowRawRename] at hi'
  simp only [graph3Rename,numeral,zRelabel] at hs'
  exact consRightInverse (raw.relabel j) (shifted.relabel j) (d.relabel j) (k.relabel j)
    tau first second hi' hc hs'

theorem numberedTagRightInverse (raw shifted d k : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (BelowRaw (fold .shift) (fold .erase) raw)))
    (ht : Nonempty (Derivation body Delta (graph1 rawTag (numeral 5) raw)))
    (hs : Nonempty (Derivation body Delta (graph3 (fold .shift) shifted (numeral 0) k raw))) :
    Nonempty (Derivation body Delta (graph3 (fold .erase) raw d k shifted)) := by
  apply numberedCases raw _ ht
  intro beta j Theta label head tau base types extras hj hc
  rw [graph3Rename]
  have hi' := renameInto hi j Theta hj
  have hs' := renameInto hs j Theta hj
  rw [belowRawRename] at hi'
  simp only [graph3Rename,numeral,zRelabel] at hs'
  exact numberedRightInverse (raw.relabel j) (shifted.relabel j) (d.relabel j) (k.relabel j)
    label head tau base types extras hi' hc hs'

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalCancellationTagsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalCancellationTagsProof
