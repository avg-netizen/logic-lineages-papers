module
public import LogicLineages.CartierObserverCurrent.FractionSeriesDefinitions
public import LogicLineages.CartierObserverCurrent.MixedProperDefinitions
public import Mathlib.Algebra.Field.ZMod

@[expose] public section
namespace LogicLineages.CartierObserverCurrent.RegularSelectors

def regular (f : RatFunc (ZMod 2)) : Prop := f.denom.eval 0 ≠ 0

/-- The genuine canonical rational power-series expansion, not a coefficient oracle. -/
noncomputable def expansion (f : RatFunc (ZMod 2)) : PowerSeries (ZMod 2) :=
  FractionSeries.seriesFraction f.num f.denom
end LogicLineages.CartierObserverCurrent.RegularSelectors
