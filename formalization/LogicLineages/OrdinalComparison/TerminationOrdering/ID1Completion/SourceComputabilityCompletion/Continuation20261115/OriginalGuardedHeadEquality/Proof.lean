module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalGuardedHeadEquality.HeadProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalGuardedHeadEquality.EqualityProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalGuardedHeadEquality.Proof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)

theorem guardHeads : Targets.InternalGuardHeads := by
  intro n numbered body alpha Delta source target k l f g tau upsilon base dest ts us extras otherExtras node answers param hs ht hn hv
  have hc := InternalAcceptanceConjunctionProof.conjunctionRecover
    (OriginalDecodedLayerCalibration.nodeAccepted n) (OriginalDecodedLayerCalibration.windowAccepted n)
    ![node,answers,param] hv
  have hd := OriginalDecodedLayerCalibration.InternalProof.nodeForward n node answers param source target hn (andLeft hc)
  exact andIntro (HeadProof.headAccepted n numbered source k f tau base ts extras hs (andLeft hd))
    (HeadProof.headAccepted n numbered target l g upsilon dest us otherExtras ht (andRight hd))

theorem guardedEquality : Targets.InternalGuardedEquality := by
  intro n numbered body alpha Delta source target k l f g tau upsilon base dest ts us extras otherExtras node answers param hs ht hn hv
  have hh := guardHeads n numbered body alpha Delta source target k l f g tau upsilon base dest ts us extras otherExtras node answers param hs ht hn hv
  have hr := EqualityProof.accepted n f g (andLeft hh) (andRight hh)
  constructor
  · intro he
    obtain ⟨hi⟩ := andLeft hr
    obtain ⟨he⟩ := he
    exact ⟨Derivation.implicationElimination hi he⟩
  · intro he
    obtain ⟨hi⟩ := andRight hr
    obtain ⟨he⟩ := he
    exact ⟨Derivation.implicationElimination hi he⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalGuardedHeadEquality.Proof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalGuardedHeadEquality.Proof
