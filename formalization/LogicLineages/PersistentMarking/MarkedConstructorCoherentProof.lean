import LogicLineages.PersistentMarking.MarkedConstructorTargets
import LogicLineages.PersistentMarking.MarkedConstructorParameterProof

namespace LogicLineages.PersistentMarking.MarkedConstructorCoherentProof
open MarkedConstructorTargets

theorem coherent : Coherent := by
  intro S E heads M p Δ _ _ hp hd he Θ ht hf
  have hw := MarkedConstructorParameterProof.weakenComposition E heads p Δ Θ hp hd ht he hf
  refine ⟨rfl, ?_, ?_⟩
  · intro t _
    simp only [MarkedConstructorValue.build, hw, and_self]
  · intro ds τ _ xs _
    simp only [MarkedConstructorValue.build, hw]
    rfl

theorem exact_Coherent : Coherent := coherent
#print axioms exact_Coherent
end LogicLineages.PersistentMarking.MarkedConstructorCoherentProof
