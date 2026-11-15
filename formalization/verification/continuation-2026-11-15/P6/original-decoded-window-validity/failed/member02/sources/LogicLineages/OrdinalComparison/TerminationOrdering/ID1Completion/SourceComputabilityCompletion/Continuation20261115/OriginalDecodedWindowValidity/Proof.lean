module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedWindowValidity.CoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedWindowValidity.Proof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationStepPeelSupportProof (andLeft andRight)
theorem internalSymbols : Targets.InternalSymbols := by
  intro n body alpha Delta raw
  have h := BindingProof.rawInduction (body := body) (Delta := Delta) n raw
    (fun _ _ r ih => CoreProof.rawStep n r ih)
  constructor
  · intro hv
    obtain ⟨hf⟩ := andLeft h
    obtain ⟨hv⟩ := hv
    exact ⟨Derivation.implicationElimination hf hv⟩
  · intro hm
    obtain ⟨hb⟩ := andRight h
    obtain ⟨hm⟩ := hm
    exact ⟨Derivation.implicationElimination hb hm⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedWindowValidity.Proof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedWindowValidity.Proof
