module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.InductionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.Proof
open InternalApplicationStepPeelSupportProof (andIntro)

theorem term : Targets.InternalTerm := by
  intro n arity body alpha Delta typ source target gamma context symbols types window node
    hcontext hsymbols htypes hwindow hnode hsource htarget hexchange ha hp
  exact InductionProof.preserved n arity false source target node window typ gamma context symbols types
    (andIntro hcontext (andIntro hsymbols (andIntro htypes hwindow)))
    (andIntro hnode (andIntro hsource (andIntro htarget hexchange))) ha hp

theorem arguments : Targets.InternalArguments := by
  intro n arity body alpha Delta typ source target gamma context symbols types window node
    hcontext hsymbols htypes hwindow hnode hsource htarget hexchange ha hp
  exact InductionProof.preserved n arity true source target node window typ gamma context symbols types
    (andIntro hcontext (andIntro hsymbols (andIntro htypes hwindow)))
    (andIntro hnode (andIntro hsource (andIntro htarget hexchange))) ha hp

theorem plainAwareExchangeUniverse : Targets.InternalPlainAwareExchangeUniverse := ⟨term,arguments⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.Proof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.Proof
