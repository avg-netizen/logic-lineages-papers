module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedNumberedRecurrence.WitnessProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedNumberedRecurrence.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedNumberedRecurrence.Proof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
theorem numberedRecurrence : Targets.InternalNumbered := by
  intro n arity body alpha Delta source target k l f g tau upsilon base dest ts us extras otherExtras node first last param symbols types hs ht hn hp0 hp3 hw
  constructor
  · intro he
    have hg := OriginalDecodedLambdaRecurrence.SuccessProof.guardNecessary n arity node param he
    have hc := WitnessProof.accepted n arity source target k l f g tau upsilon base dest ts us extras otherExtras node first last param symbols types hs ht hn hp0 hp3 hw hg
    obtain ⟨hf⟩ := andLeft hc
    obtain ⟨he⟩ := he
    exact andIntro hg ⟨Derivation.implicationElimination hf he⟩
  · intro h
    have hg := andLeft h
    have hc := WitnessProof.accepted n arity source target k l f g tau upsilon base dest ts us extras otherExtras node first last param symbols types hs ht hn hp0 hp3 hw hg
    obtain ⟨hf⟩ := andRight hc
    obtain ⟨hr⟩ := andRight h
    exact ⟨Derivation.implicationElimination hf hr⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedNumberedRecurrence.Proof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedNumberedRecurrence.Proof
