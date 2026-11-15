module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalValidHeadEncodingInjectivity.CoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalValidHeadEncodingInjectivity.Proof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalControlGraphSupportProof
open Continuation20261114

theorem validEncoding : Targets.InternalValidEncoding := by
  intro n body alpha Delta f g ef eg hf hg hef heg
  constructor
  · intro he
    exact CoreProof.forward n f g ef eg hf hg hef heg he
  · intro he
    have ht := headTransport OriginalHeadEncodingBridge.encodeHead ef f g Fin.elim0 he hef
    exact valueUnique OriginalHeadEncodingBridge.encodeHead ef eg ![g] ht heg
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalValidHeadEncodingInjectivity.Proof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalValidHeadEncodingInjectivity.Proof
