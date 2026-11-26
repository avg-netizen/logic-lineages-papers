module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedBinaryRecurrence.WitnessProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedBinaryRecurrence.Proof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
theorem binaryRecurrence : Targets.InternalBinary := by
  intro n arity body alpha Delta cons source target sigma tau q a r b node first last param hs ht hn hp0 hp3
  constructor
  · intro he
    have hg := OriginalDecodedLambdaRecurrence.SuccessProof.guardNecessary n arity node param he
    have hc := WitnessProof.accepted n arity cons source target sigma tau q a r b node first last param hs ht hn hp0 hp3 hg
    obtain ⟨hf⟩ := andLeft hc
    obtain ⟨he⟩ := he
    exact andIntro hg ⟨Derivation.implicationElimination hf he⟩
  · intro h
    have hg := andLeft h
    have hc := WitnessProof.accepted n arity cons source target sigma tau q a r b node first last param hs ht hn hp0 hp3 hg
    obtain ⟨hf⟩ := andRight hc
    obtain ⟨hr⟩ := andRight h
    exact ⟨Derivation.implicationElimination hf hr⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedBinaryRecurrence.Proof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedBinaryRecurrence.Proof
