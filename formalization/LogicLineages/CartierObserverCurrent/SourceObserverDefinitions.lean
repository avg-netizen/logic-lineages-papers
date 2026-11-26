module
public import LogicLineages.CartierObserverCurrent.AllWordObserverDefinitions
public import LogicLineages.CartierObserverCurrent.SourceStateDefinitions

@[expose] public section
namespace LogicLineages.CartierObserverCurrent.SourceObserver

noncomputable def initial (d : Nat) (P : Polynomial (ZMod 2)) : RatFunc (ZMod 2) :=
  FractionSeries.rationalFraction P (SourceBudget.denominator (ZMod 2) d)
end LogicLineages.CartierObserverCurrent.SourceObserver
