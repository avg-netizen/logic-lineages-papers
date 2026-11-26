module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankTransportBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankUnaryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorBoundsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankTransportOrdinaryProof
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
open OriginalRawVariableRankTransportBindingProof OriginalRawVariableRankTransportSyntaxProof
open OriginalRawVariableRankUnaryProof
open OriginalRawSyntaxTransportInternalParametersQueryProof
open OriginalRawSyntaxTransportInternalFoldOrdinaryProof OriginalRawSyntaxTransportInternalFoldConstructorFieldsProof
open OriginalRawSyntaxTransportInternalConstructorBoundsProof

theorem ordinaryTransformShape (erasing : Bool) (raw transformed d k head child childOut : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 ordinaryConstructor raw head child)))
    (hchild : Nonempty (Derivation body Delta (graph3 (fold (transformMode erasing)) childOut d (k) child)))
    (ht : Nonempty (Derivation body Delta (graph3 (fold (transformMode erasing)) transformed d k raw))) :
    Nonempty (Derivation body Delta (graph2 ordinaryConstructor transformed head childOut)) := by
  cases erasing <;> exact ordinaryForward _ raw transformed d k head child childOut hc hchild ht

theorem ordinaryTransportAt (erasing : Bool) (raw transformed before after d k head child childOut : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (BelowRaw (fold (transformMode erasing)) erasing raw)))
    (hc : Nonempty (Derivation body Delta (graph2 ordinaryConstructor raw head child)))
    (hchild : Nonempty (Derivation body Delta (graph3 (fold (transformMode erasing)) childOut d (k) child)))
    (ht : Nonempty (Derivation body Delta (graph3 (fold (transformMode erasing)) transformed d k raw)))
    (hb : Nonempty (Derivation body Delta (graph1 variableRankRaw before raw)))
    (ha : Nonempty (Derivation body Delta (graph1 variableRankRaw after transformed))) :
    Nonempty (Derivation body Delta (RankRelation erasing after before)) := by
  have hf := ordinaryFields raw k head child hc
  have hl := unaryChildStrict raw child (andLeft hf) (andLeft (andRight hf))
  have hshape := ordinaryTransformShape erasing raw transformed d k head child childOut hc hchild ht
  exact belowRawApply (fold (transformMode erasing)) erasing raw child d (k) childOut before after hi hl hchild
    (rankOrdinaryForward raw before head child hc hb)
    (rankOrdinaryForward transformed after head childOut hshape ha)

theorem ordinaryTransport (erasing : Bool) (raw transformed before after d k head child : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (BelowRaw (fold (transformMode erasing)) erasing raw)))
    (hc : Nonempty (Derivation body Delta (graph2 ordinaryConstructor raw head child)))
    (ht : Nonempty (Derivation body Delta (graph3 (fold (transformMode erasing)) transformed d k raw)))
    (hb : Nonempty (Derivation body Delta (graph1 variableRankRaw before raw)))
    (ha : Nonempty (Derivation body Delta (graph1 variableRankRaw after transformed))) :
    Nonempty (Derivation body Delta (RankRelation erasing after before)) := by
  apply ternaryCases (fold (transformMode erasing)) d (k) child _
  intro beta j Theta childOut hj hchild
  rw [rankRelationRename]
  have hi' := renameInto hi j Theta hj
  have hc' := renameInto hc j Theta hj
  have ht' := renameInto ht j Theta hj
  have hb' := renameInto hb j Theta hj
  have ha' := renameInto ha j Theta hj
  rw [belowRawRename] at hi'
  rw [graph2Rename] at hc'
  rw [graph3Rename] at ht'
  rw [graph1Rename] at hb' ha'
  exact ordinaryTransportAt erasing (raw.relabel j) (transformed.relabel j) (before.relabel j) (after.relabel j)
    (d.relabel j) (k.relabel j) (head.relabel j) (child.relabel j) childOut hi' hc' hchild ht' hb' ha'

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankTransportOrdinaryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankTransportOrdinaryProof
