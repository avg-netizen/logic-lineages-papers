module

public import LogicLineages.Ultrafilters.HamelDefinitions

@[expose] public section

namespace LogicLineages.Ultrafilters.Targets

/-- Paper 11, lem:length, in the actual second case of the Hamel dichotomy.
The coordinate-zero premise is precisely that case, not an assumed support
growth theorem or an assumed construction of the final witness. -/
def HamelLengthEscapes : Prop :=
  ∀ {ι : Type*} (B : Module.Basis ι ℚ ℝ) (p : Ultrafilter ℝ),
    Admissible p → (∀ i, {x | B.repr x i = 0} ∈ p) →
    (∀ k : Nat, {x | supportLength B x = k} ∉ p) ∧
      ∀ m : Nat, {x | m < supportLength B x} ∈ p

end LogicLineages.Ultrafilters.Targets
