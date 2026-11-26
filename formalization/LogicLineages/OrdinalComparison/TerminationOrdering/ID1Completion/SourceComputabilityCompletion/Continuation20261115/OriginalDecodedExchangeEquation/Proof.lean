module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedExchangeEquation.EquationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedExchangeEquation.Proof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationStepPeelSupportProof (andLeft andRight)
theorem previousAnswers : Targets.InternalPreviousAnswers := by
  intro n arity body alpha Delta node param rank old deps values hr ho hd
  have ha := OwnProof.agreement n arity node param rank old deps hr ho hd
  exact ⟨fun hv => MapProof.transport (exchange n arity) deps param old values ha hv,
    fun hv => MapProof.reverseTransport (exchange n arity) deps param old values ha hv⟩

theorem exchangeEquation : Targets.InternalExchangeEquation := by
  intro n arity body alpha Delta node param values value ha
  have h := EquationProof.equation n arity node param values value ha
  constructor
  · intro he
    obtain ⟨hf⟩ := andLeft h
    obtain ⟨he⟩ := he
    exact ⟨Derivation.implicationElimination hf he⟩
  · intro hg
    obtain ⟨hf⟩ := andRight h
    obtain ⟨hg⟩ := hg
    exact ⟨Derivation.implicationElimination hf hg⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedExchangeEquation.Proof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedExchangeEquation.Proof
