module
public import LogicLineages.CartierObserverCurrent.SplitSupportProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.CartierObserverCurrent.SplitSupport.StatementChecks

theorem fixed_productRoots : Targets.ProductRoots :=
  LogicLineages.CartierObserverCurrent.SplitSupport.productRoots

theorem fixed_splitDivisibility : Targets.SplitDivisibility :=
  LogicLineages.CartierObserverCurrent.SplitSupport.splitDivisibility

theorem fixed_sourceSimpleDivisor : Targets.SourceSimpleDivisor :=
  LogicLineages.CartierObserverCurrent.SplitSupport.sourceSimpleDivisor

#audit_namespace LogicLineages.CartierObserverCurrent.SplitSupport.StatementChecks
end LogicLineages.CartierObserverCurrent.SplitSupport.StatementChecks
