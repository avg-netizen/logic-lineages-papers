module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankTransportQueryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankTransportArithmeticProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorBoundsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankTransportApplicationProof
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
open OriginalRawVariableRankSupportProof OriginalRawVariableRankApplicationProof
open OriginalRawVariableRankTransportQueryProof OriginalRawVariableRankTransportArithmeticProof
open OriginalRawSyntaxTransportInternalFoldApplicationProof OriginalRawSyntaxTransportInternalFoldConstructorFieldsProof
open OriginalRawSyntaxTransportInternalConstructorBoundsProof

theorem applicationTransformShape (erasing : Bool) (raw transformed d k domain first second firstOut secondOut : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 applicationConstructor raw domain first second)))
    (hfirst : Nonempty (Derivation body Delta (graph3 (fold (transformMode erasing)) firstOut d k first)))
    (hsecond : Nonempty (Derivation body Delta (graph3 (fold (transformMode erasing)) secondOut d k second)))
    (ht : Nonempty (Derivation body Delta (graph3 (fold (transformMode erasing)) transformed d k raw))) :
    Nonempty (Derivation body Delta (graph3 applicationConstructor transformed domain firstOut secondOut)) := by
  cases erasing <;> exact applicationForward _ raw transformed d k domain first second firstOut secondOut hc hfirst hsecond ht

theorem applicationTransportAt (erasing : Bool)
    (raw transformed before after d k domain first second firstOut secondOut beforeFirst beforeSecond afterFirst afterSecond : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (BelowRaw (fold (transformMode erasing)) erasing raw)))
    (hc : Nonempty (Derivation body Delta (graph3 applicationConstructor raw domain first second)))
    (hfirst : Nonempty (Derivation body Delta (graph3 (fold (transformMode erasing)) firstOut d k first)))
    (hsecond : Nonempty (Derivation body Delta (graph3 (fold (transformMode erasing)) secondOut d k second)))
    (hbFirst : Nonempty (Derivation body Delta (graph1 variableRankRaw beforeFirst first)))
    (hbSecond : Nonempty (Derivation body Delta (graph1 variableRankRaw beforeSecond second)))
    (haFirst : Nonempty (Derivation body Delta (graph1 variableRankRaw afterFirst firstOut)))
    (haSecond : Nonempty (Derivation body Delta (graph1 variableRankRaw afterSecond secondOut)))
    (ht : Nonempty (Derivation body Delta (graph3 (fold (transformMode erasing)) transformed d k raw)))
    (hb : Nonempty (Derivation body Delta (graph1 variableRankRaw before raw)))
    (ha : Nonempty (Derivation body Delta (graph1 variableRankRaw after transformed))) :
    Nonempty (Derivation body Delta (RankRelation erasing after before)) := by
  have hf := applicationFields raw domain first second hc
  have hl := binaryChildrenStrict raw first second (andLeft hf) (andLeft (andRight hf)) (andRight (andRight hf))
  have hrf := belowRawApply (fold (transformMode erasing)) erasing raw first d k firstOut beforeFirst afterFirst
    hi (andLeft hl) hfirst hbFirst haFirst
  have hrs := belowRawApply (fold (transformMode erasing)) erasing raw second d k secondOut beforeSecond afterSecond
    hi (andRight hl) hsecond hbSecond haSecond
  have hshape := applicationTransformShape erasing raw transformed d k domain first second firstOut secondOut hc hfirst hsecond ht
  have hbefore := rankSumForward before first second beforeFirst beforeSecond hbFirst hbSecond
    (rankApplicationForward raw before domain first second hc hb)
  have hafter := rankSumForward after firstOut secondOut afterFirst afterSecond haFirst haSecond
    (rankApplicationForward transformed after domain firstOut secondOut hshape ha)
  exact relationAddition erasing after before afterFirst beforeFirst afterSecond beforeSecond hafter hbefore hrf hrs

theorem applicationTransport (erasing : Bool) (raw transformed before after d k domain first second : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (BelowRaw (fold (transformMode erasing)) erasing raw)))
    (hc : Nonempty (Derivation body Delta (graph3 applicationConstructor raw domain first second)))
    (ht : Nonempty (Derivation body Delta (graph3 (fold (transformMode erasing)) transformed d k raw)))
    (hb : Nonempty (Derivation body Delta (graph1 variableRankRaw before raw)))
    (ha : Nonempty (Derivation body Delta (graph1 variableRankRaw after transformed))) :
    Nonempty (Derivation body Delta (RankRelation erasing after before)) := by
  apply binaryTransportCases (fold (transformMode erasing)) variableRankRaw d k first second _
  intro beta j Theta firstOut secondOut beforeFirst beforeSecond afterFirst afterSecond hj hfirst hsecond hbFirst hbSecond haFirst haSecond
  rw [rankRelationRename]
  have hi' := renameInto hi j Theta hj
  have hc' := renameInto hc j Theta hj
  have ht' := renameInto ht j Theta hj
  have hb' := renameInto hb j Theta hj
  have ha' := renameInto ha j Theta hj
  rw [belowRawRename] at hi'
  rw [graph3Rename] at hc'
  rw [graph3Rename] at ht'
  rw [graph1Rename] at hb' ha'
  exact applicationTransportAt erasing (raw.relabel j) (transformed.relabel j) (before.relabel j) (after.relabel j)
    (d.relabel j) (k.relabel j) (domain.relabel j) (first.relabel j) (second.relabel j) firstOut secondOut beforeFirst beforeSecond afterFirst afterSecond
    hi' hc' hfirst hsecond hbFirst hbSecond haFirst haSecond ht' hb' ha'

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankTransportApplicationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankTransportApplicationProof
