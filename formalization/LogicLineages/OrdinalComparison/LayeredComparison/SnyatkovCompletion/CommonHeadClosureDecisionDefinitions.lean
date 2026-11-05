module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BaseBooleanSourceDefinitions
public import LogicLineages.OrdinalComparison.LayeredComparison.CommonLayerComparisonDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.CommonHeadClosureDecision

abbrev Input := List Nat × (Nat × (Nat × Int))

/-- Compose the existing all-code comparison compiler with the actual BASE
postfix bridge and source closure decision. No source comparator is supplied. -/
noncomputable def existsAnswer (p : Input) : Option Bool :=
  BaseBooleanSource.Code.decideClosureExists
    (CommonLayerComparison.compileCode p.1 p.2.1 p.2.2.1 p.2.2.2)
noncomputable def forallAnswer (p : Input) : Option Bool :=
  BaseBooleanSource.Code.decideClosureForall
    (CommonLayerComparison.compileCode p.1 p.2.1 p.2.2.1 p.2.2.2)

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.CommonHeadClosureDecision
