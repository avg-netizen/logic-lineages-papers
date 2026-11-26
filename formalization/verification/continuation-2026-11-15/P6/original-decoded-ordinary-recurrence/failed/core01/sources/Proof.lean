module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedOrdinaryRecurrence.WitnessProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedOrdinaryRecurrence.Proof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
theorem ordinaryRecurrence : Targets.InternalOrdinary := by
  intro n arity body alpha Delta source target f g base dest node child param symbols types hs ht hn hp hw
  constructor
  · intro he
    have hg := OriginalDecodedLambdaRecurrence.SuccessProof.guardNecessary n arity node param he
    have hc := WitnessProof.accepted n arity source target f g base dest node child param symbols types hs ht hn hp hw hg
    obtain ⟨hf⟩ := andLeft hc
    obtain ⟨he⟩ := he
    exact andIntro hg ⟨Derivation.implicationElimination hf he⟩
  · intro h
    have hg := andLeft h
    have hc := WitnessProof.accepted n arity source target f g base dest node child param symbols types hs ht hn hp hw hg
    obtain ⟨hf⟩ := andRight hc
    obtain ⟨hr⟩ := andRight h
    exact ⟨Derivation.implicationElimination hf hr⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedOrdinaryRecurrence.Proof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedOrdinaryRecurrence.Proof
