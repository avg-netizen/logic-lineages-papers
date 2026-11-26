module
public import LogicLineages.CartierObserverCurrent.BasicRationalDefinitions

@[expose] public section
universe u
namespace LogicLineages.CartierObserverCurrent.MixedProper

/-- Genuine reduced-fraction properness, including zero. -/
def proper {K : Type u} [Field K] (f : RatFunc K) : Prop :=
  f.num.degree < f.denom.degree

/-- Literal source selectors on actual rational differentials. -/
noncomputable def step {K : Type u} [Field K] [CharP K 2] [PerfectRing K 2]
    (b : Bool) (f : RatFunc K) : RatFunc K :=
  if b then Basic.actualDifferentialCartier f
  else Basic.actualDifferentialCartier (Basic.rationalX * f)
end LogicLineages.CartierObserverCurrent.MixedProper
