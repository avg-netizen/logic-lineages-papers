module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedLambdaRecurrence.CoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedLambdaRecurrence.SuccessProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedLambdaRecurrence.Proof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
theorem lambdaRecurrence : Targets.InternalLambda := by
  intro n arity body alpha Delta source target sigma tau q r node child param hs ht hn hp
  constructor
  · intro he
    have hg := SuccessProof.guardNecessary n arity node param he
    have hc := CoreProof.accepted n arity source target sigma tau q r node child param hs ht hn hp hg
    obtain ⟨hf⟩ := andLeft hc
    obtain ⟨he⟩ := he
    exact andIntro hg ⟨Derivation.implicationElimination hf he⟩
  · intro h
    have hg := andLeft h
    have hc := CoreProof.accepted n arity source target sigma tau q r node child param hs ht hn hp hg
    obtain ⟨hf⟩ := andRight hc
    obtain ⟨hr⟩ := andRight h
    exact ⟨Derivation.implicationElimination hf hr⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedLambdaRecurrence.Proof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedLambdaRecurrence.Proof
