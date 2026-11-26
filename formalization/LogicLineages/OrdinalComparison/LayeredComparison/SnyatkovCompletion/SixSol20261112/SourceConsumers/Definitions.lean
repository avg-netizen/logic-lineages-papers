module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SixSol20261112.SourceDecisionWorkingDefinitions
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.CommonHeadFirstOrderDefinitions
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BalancedFirstOrderDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SixSol20261112.SourceConsumers

/-- Compose the actual accepted original arithmetic algorithm with the exact
original common-head first-order translator. No solver is a runtime premise. -/
noncomputable def commonAnswer (code : Nat) : Bool :=
  SourceDecision.answer (CommonHeadFirstOrder.Code.translate code)

/-- The original balanced translator retains each whole pair certificate and
positive binder. It is composed with the same concrete proved BASE algorithm. -/
noncomputable def balancedAnswer (code : Nat) : Bool :=
  SourceDecision.answer (BalancedFirstOrder.Code.translate code)

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SixSol20261112.SourceConsumers
