module

public import LogicLineages.Ultrafilters.HamelDefinitions

@[expose] public section

namespace LogicLineages.Ultrafilters

noncomputable def supportDecay {ι : Type*} (B : Module.Basis ι ℚ ℝ)
    (x : ℝ) : ℝ := (1 / 2 : ℝ) ^ supportLength B x

end LogicLineages.Ultrafilters
