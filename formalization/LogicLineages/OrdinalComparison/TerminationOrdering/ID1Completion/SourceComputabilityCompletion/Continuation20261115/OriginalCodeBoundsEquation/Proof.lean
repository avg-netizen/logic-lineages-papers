module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeBoundsEquation.EquationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeBoundsEquation.Proof
open OriginalDecodedExchangeEquation
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationStepPeelSupportProof (andLeft andRight)
theorem previousAnswers : Targets.InternalPreviousAnswers := by
  intro n body alpha Delta node param old deps values ho hd
  have ha := OwnProof.agreement n node param node old deps (OriginalCodeBoundsCacheCoherence.RankProof.rankValue node param) ho hd
  exact ⟨fun hv => MapProof.transport (OriginalCodeBoundsRecursion.extract n) deps param old values ha hv,
    fun hv => MapProof.reverseTransport (OriginalCodeBoundsRecursion.extract n) deps param old values ha hv⟩

theorem exchangeEquation : Targets.InternalBoundsEquation := by
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
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeBoundsEquation.Proof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeBoundsEquation.Proof
