module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedBooleanRange.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.HeadWindowBooleanRange.ProgramRangeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedBooleanRange.LayerRangeProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114
open HeadWindowBooleanRange.ProgramRangeProof

theorem anyRange (p q : Program 19) : Ranged (ExchangeLayer.any p q) :=
  branchRange _ _ _ (normalizeRange q) (normalizeRange p)

theorem lambdaRange : Ranged ExchangeLayer.lambdaCase := conjunctionRange _ _
theorem applicationRange : Ranged ExchangeLayer.applicationCase := conjunctionRange _ _
theorem ordinaryRange : Ranged ExchangeLayer.ordinaryCase := anyRange _ _
theorem numberedRange : Ranged ExchangeLayer.numberedCase := conjunctionRange _ _

theorem chooseRange (p yes no : Program 19) (hy : Ranged yes) (hn : Ranged no) :
    Ranged (ExchangeLayer.choose p yes no) := branchRange p no yes hn hy

theorem layerRange : Ranged ExchangeLayer.layer :=
  chooseRange _ _ _
    (chooseRange _ _ _ lambdaRange
      (chooseRange _ _ _ applicationRange
        (chooseRange _ _ _ ordinaryRange
          (chooseRange _ _ _ numberedRange
            (chooseRange _ _ _ applicationRange (constantRange 19 0))))))
    (constantRange 19 0)

theorem bodyRange (U : Fin 19 → Program 3) : Ranged (TransparentExchangeLayer.body U) :=
  compositionRange ExchangeLayer.layer (TransparentExchangeLayer.fields U) layerRange
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedBooleanRange.LayerRangeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedBooleanRange.LayerRangeProof
