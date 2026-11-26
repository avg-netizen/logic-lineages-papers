module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Equation.EquationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Equation.Proof
open Continuation20261115.OriginalDecodedExchangeEquation
open Continuation20261115
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationStepPeelSupportProof (andLeft andRight)
theorem previousAnswers : Targets.InternalPreviousAnswers := by
  intro n body alpha Delta node param nodeRank old deps values hr ho hd
  have ha := OwnProof.agreement n node param nodeRank old deps hr ho hd
  exact ⟨fun hv => MapProof.transport (OriginalEnumerationFields.extract n) deps param old values ha hv,
    fun hv => MapProof.reverseTransport (OriginalEnumerationFields.extract n) deps param old values ha hv⟩

theorem exchangeEquation : Targets.InternalFieldsEquation := by
  intro n body alpha Delta node param values value ha
  have h := EquationProof.equation n node param values value ha
  constructor
  · intro he
    obtain ⟨hf⟩ := andLeft h
    obtain ⟨he⟩ := he
    exact ⟨Derivation.implicationElimination hf he⟩
  · intro hg
    obtain ⟨hf⟩ := andRight h
    obtain ⟨hg⟩ := hg
    exact ⟨Derivation.implicationElimination hf hg⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Equation.Proof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Equation.Proof
