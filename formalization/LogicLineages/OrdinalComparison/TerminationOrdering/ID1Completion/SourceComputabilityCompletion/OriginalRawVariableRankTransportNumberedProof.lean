module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankTransportQueryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankTransportArithmeticProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankNumberedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorBoundsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalCancellationNumberedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankTransportNumberedProof
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
open OriginalRawVariableRankSupportProof OriginalRawVariableRankNumberedProof
open OriginalRawVariableRankTransportQueryProof OriginalRawVariableRankTransportArithmeticProof
open OriginalRawSyntaxTransportInternalFoldNumberedProof OriginalRawSyntaxTransportInternalFoldConstructorFieldsProof
open OriginalRawSyntaxTransportInternalConstructorBoundsProof

theorem numberedTransformShape (erasing : Bool) (raw transformed d k label head tau base types extras firstOut secondOut : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (programGraph numberedConstructor raw ![label,head,tau,base,types,extras])))
    (hfirst : Nonempty (Derivation body Delta (graph3 (fold (transformMode erasing)) firstOut d k base)))
    (hsecond : Nonempty (Derivation body Delta (graph3 (fold (transformMode erasing)) secondOut d k extras)))
    (ht : Nonempty (Derivation body Delta (graph3 (fold (transformMode erasing)) transformed d k raw))) :
    Nonempty (Derivation body Delta (programGraph numberedConstructor transformed ![label,head,tau,firstOut,types,secondOut])) := by
  cases erasing <;> exact numberedForward _ raw transformed d k label head tau base types extras firstOut secondOut hc hfirst hsecond ht

theorem numberedTransportAt (erasing : Bool)
    (raw transformed before after d k label head tau base types extras firstOut secondOut beforeFirst beforeSecond afterFirst afterSecond : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (BelowRaw (fold (transformMode erasing)) erasing raw)))
    (hc : Nonempty (Derivation body Delta (programGraph numberedConstructor raw ![label,head,tau,base,types,extras])))
    (hfirst : Nonempty (Derivation body Delta (graph3 (fold (transformMode erasing)) firstOut d k base)))
    (hsecond : Nonempty (Derivation body Delta (graph3 (fold (transformMode erasing)) secondOut d k extras)))
    (hbFirst : Nonempty (Derivation body Delta (graph1 variableRankRaw beforeFirst base)))
    (hbSecond : Nonempty (Derivation body Delta (graph1 variableRankRaw beforeSecond extras)))
    (haFirst : Nonempty (Derivation body Delta (graph1 variableRankRaw afterFirst firstOut)))
    (haSecond : Nonempty (Derivation body Delta (graph1 variableRankRaw afterSecond secondOut)))
    (ht : Nonempty (Derivation body Delta (graph3 (fold (transformMode erasing)) transformed d k raw)))
    (hb : Nonempty (Derivation body Delta (graph1 variableRankRaw before raw)))
    (ha : Nonempty (Derivation body Delta (graph1 variableRankRaw after transformed))) :
    Nonempty (Derivation body Delta (RankRelation erasing after before)) := by
  have hf := numberedFields raw label head tau base types extras hc
  have hl := binaryChildrenStrict raw base extras (andLeft hf) (andLeft (andRight hf)) (andRight (andRight hf))
  have hrf := belowRawApply (fold (transformMode erasing)) erasing raw base d k firstOut beforeFirst afterFirst
    hi (andLeft hl) hfirst hbFirst haFirst
  have hrs := belowRawApply (fold (transformMode erasing)) erasing raw extras d k secondOut beforeSecond afterSecond
    hi (andRight hl) hsecond hbSecond haSecond
  have hshape := numberedTransformShape erasing raw transformed d k label head tau base types extras firstOut secondOut hc hfirst hsecond ht
  have hbefore := rankSumForward before base extras beforeFirst beforeSecond hbFirst hbSecond
    (rankNumberedForward raw before label head tau base types extras hc hb)
  have hafter := rankSumForward after firstOut secondOut afterFirst afterSecond haFirst haSecond
    (rankNumberedForward transformed after label head tau firstOut types secondOut hshape ha)
  exact relationAddition erasing after before afterFirst beforeFirst afterSecond beforeSecond hafter hbefore hrf hrs

theorem numberedTransport (erasing : Bool) (raw transformed before after d k label head tau base types extras : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (BelowRaw (fold (transformMode erasing)) erasing raw)))
    (hc : Nonempty (Derivation body Delta (programGraph numberedConstructor raw ![label,head,tau,base,types,extras])))
    (ht : Nonempty (Derivation body Delta (graph3 (fold (transformMode erasing)) transformed d k raw)))
    (hb : Nonempty (Derivation body Delta (graph1 variableRankRaw before raw)))
    (ha : Nonempty (Derivation body Delta (graph1 variableRankRaw after transformed))) :
    Nonempty (Derivation body Delta (RankRelation erasing after before)) := by
  apply binaryTransportCases (fold (transformMode erasing)) variableRankRaw d k base extras _
  intro beta j Theta firstOut secondOut beforeFirst beforeSecond afterFirst afterSecond hj hfirst hsecond hbFirst hbSecond haFirst haSecond
  rw [rankRelationRename]
  have hi' := renameInto hi j Theta hj
  have hc' := renameInto hc j Theta hj
  have ht' := renameInto ht j Theta hj
  have hb' := renameInto hb j Theta hj
  have ha' := renameInto ha j Theta hj
  rw [belowRawRename] at hi'
  simp only [programRename,OriginalRawSyntaxTransportInternalCancellationNumberedProof.tupleSixRename] at hc'
  rw [graph3Rename] at ht'
  rw [graph1Rename] at hb' ha'
  exact numberedTransportAt erasing (raw.relabel j) (transformed.relabel j) (before.relabel j) (after.relabel j)
    (d.relabel j) (k.relabel j) (label.relabel j) (head.relabel j) (tau.relabel j) (base.relabel j) (types.relabel j) (extras.relabel j) firstOut secondOut beforeFirst beforeSecond afterFirst afterSecond
    hi' hc' hfirst hsecond hbFirst hbSecond haFirst haSecond ht' hb' ha'

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankTransportNumberedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankTransportNumberedProof
