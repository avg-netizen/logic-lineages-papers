module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankTransportLambdaProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankTransportOrdinaryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankTransportApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankTransportConsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankTransportNumberedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserUnaryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserBinaryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserNumberedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankTransportTagsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open InternalTagArithmeticSupportProof (refl symm trans congSuc)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternal OriginalRawVariableRank
open OriginalRawVariableRankTransport
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
open OriginalRawVariableRankTransportSyntaxProof
open OriginalRawSyntaxTransportInternalParserUnaryProof OriginalRawSyntaxTransportInternalParserBinaryProof
open OriginalRawSyntaxTransportInternalParserNumberedProof
open OriginalRawVariableRankTransportLambdaProof
open OriginalRawVariableRankTransportOrdinaryProof
open OriginalRawVariableRankTransportApplicationProof
open OriginalRawVariableRankTransportConsProof
open OriginalRawVariableRankTransportNumberedProof

theorem lambdaTagTransport (erasing : Bool) (raw transformed before after d k : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (BelowRaw (fold (transformMode erasing)) erasing raw)))
    (htag : Nonempty (Derivation body Delta (graph1 rawTag (numeral 1) raw)))
    (ht : Nonempty (Derivation body Delta (graph3 (fold (transformMode erasing)) transformed d k raw)))
    (hb : Nonempty (Derivation body Delta (graph1 variableRankRaw before raw)))
    (ha : Nonempty (Derivation body Delta (graph1 variableRankRaw after transformed))) :
    Nonempty (Derivation body Delta (RankRelation erasing after before)) := by
  apply lambdaCases raw _ htag
  intro beta j Theta domain child hj hc
  rw [rankRelationRename]
  have hi' := renameInto hi j Theta hj
  have ht' := renameInto ht j Theta hj
  have hb' := renameInto hb j Theta hj
  have ha' := renameInto ha j Theta hj
  rw [belowRawRename] at hi'
  rw [graph3Rename] at ht'
  rw [graph1Rename] at hb' ha'
  exact lambdaTransport erasing (raw.relabel j) (transformed.relabel j)
    (before.relabel j) (after.relabel j) (d.relabel j) (k.relabel j)
    domain child hi' hc ht' hb' ha'

theorem ordinaryTagTransport (erasing : Bool) (raw transformed before after d k : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (BelowRaw (fold (transformMode erasing)) erasing raw)))
    (htag : Nonempty (Derivation body Delta (graph1 rawTag (numeral 4) raw)))
    (ht : Nonempty (Derivation body Delta (graph3 (fold (transformMode erasing)) transformed d k raw)))
    (hb : Nonempty (Derivation body Delta (graph1 variableRankRaw before raw)))
    (ha : Nonempty (Derivation body Delta (graph1 variableRankRaw after transformed))) :
    Nonempty (Derivation body Delta (RankRelation erasing after before)) := by
  apply ordinaryCases raw _ htag
  intro beta j Theta head child hj hc
  rw [rankRelationRename]
  have hi' := renameInto hi j Theta hj
  have ht' := renameInto ht j Theta hj
  have hb' := renameInto hb j Theta hj
  have ha' := renameInto ha j Theta hj
  rw [belowRawRename] at hi'
  rw [graph3Rename] at ht'
  rw [graph1Rename] at hb' ha'
  exact ordinaryTransport erasing (raw.relabel j) (transformed.relabel j)
    (before.relabel j) (after.relabel j) (d.relabel j) (k.relabel j)
    head child hi' hc ht' hb' ha'

theorem applicationTagTransport (erasing : Bool) (raw transformed before after d k : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (BelowRaw (fold (transformMode erasing)) erasing raw)))
    (htag : Nonempty (Derivation body Delta (graph1 rawTag (numeral 2) raw)))
    (ht : Nonempty (Derivation body Delta (graph3 (fold (transformMode erasing)) transformed d k raw)))
    (hb : Nonempty (Derivation body Delta (graph1 variableRankRaw before raw)))
    (ha : Nonempty (Derivation body Delta (graph1 variableRankRaw after transformed))) :
    Nonempty (Derivation body Delta (RankRelation erasing after before)) := by
  apply applicationCases raw _ htag
  intro beta j Theta domain first second hj hc
  rw [rankRelationRename]
  have hi' := renameInto hi j Theta hj
  have ht' := renameInto ht j Theta hj
  have hb' := renameInto hb j Theta hj
  have ha' := renameInto ha j Theta hj
  rw [belowRawRename] at hi'
  rw [graph3Rename] at ht'
  rw [graph1Rename] at hb' ha'
  exact applicationTransport erasing (raw.relabel j) (transformed.relabel j)
    (before.relabel j) (after.relabel j) (d.relabel j) (k.relabel j)
    domain first second hi' hc ht' hb' ha'

theorem consTagTransport (erasing : Bool) (raw transformed before after d k : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (BelowRaw (fold (transformMode erasing)) erasing raw)))
    (htag : Nonempty (Derivation body Delta (graph1 rawTag (numeral 7) raw)))
    (ht : Nonempty (Derivation body Delta (graph3 (fold (transformMode erasing)) transformed d k raw)))
    (hb : Nonempty (Derivation body Delta (graph1 variableRankRaw before raw)))
    (ha : Nonempty (Derivation body Delta (graph1 variableRankRaw after transformed))) :
    Nonempty (Derivation body Delta (RankRelation erasing after before)) := by
  apply consCases raw _ htag
  intro beta j Theta tau first second hj hc
  rw [rankRelationRename]
  have hi' := renameInto hi j Theta hj
  have ht' := renameInto ht j Theta hj
  have hb' := renameInto hb j Theta hj
  have ha' := renameInto ha j Theta hj
  rw [belowRawRename] at hi'
  rw [graph3Rename] at ht'
  rw [graph1Rename] at hb' ha'
  exact consTransport erasing (raw.relabel j) (transformed.relabel j)
    (before.relabel j) (after.relabel j) (d.relabel j) (k.relabel j)
    tau first second hi' hc ht' hb' ha'

theorem numberedTagTransport (erasing : Bool) (raw transformed before after d k : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (BelowRaw (fold (transformMode erasing)) erasing raw)))
    (htag : Nonempty (Derivation body Delta (graph1 rawTag (numeral 5) raw)))
    (ht : Nonempty (Derivation body Delta (graph3 (fold (transformMode erasing)) transformed d k raw)))
    (hb : Nonempty (Derivation body Delta (graph1 variableRankRaw before raw)))
    (ha : Nonempty (Derivation body Delta (graph1 variableRankRaw after transformed))) :
    Nonempty (Derivation body Delta (RankRelation erasing after before)) := by
  apply numberedCases raw _ htag
  intro beta j Theta label head tau base types extras hj hc
  rw [rankRelationRename]
  have hi' := renameInto hi j Theta hj
  have ht' := renameInto ht j Theta hj
  have hb' := renameInto hb j Theta hj
  have ha' := renameInto ha j Theta hj
  rw [belowRawRename] at hi'
  rw [graph3Rename] at ht'
  rw [graph1Rename] at hb' ha'
  exact numberedTransport erasing (raw.relabel j) (transformed.relabel j)
    (before.relabel j) (after.relabel j) (d.relabel j) (k.relabel j)
    label head tau base types extras hi' hc ht' hb' ha'


end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankTransportTagsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankTransportTagsProof
