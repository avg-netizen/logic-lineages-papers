module
public import LogicLineages.CartierObserverCurrent.MixedProperDefinitions

@[expose] public section
universe u
namespace LogicLineages.CartierObserverCurrent.MixedWord

/-- Actual low-bit-first mixed rational execution. -/
noncomputable def execute {K : Type u} [Field K] [CharP K 2] [PerfectRing K 2] :
    List Bool → RatFunc K → RatFunc K
  | [], f => f
  | b :: w, f => execute w (MixedProper.step b f)
end LogicLineages.CartierObserverCurrent.MixedWord
