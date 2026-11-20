import LogicLineages.PersistentMarking.NumberedWindowAddressApplicationTargets

namespace LogicLineages.PersistentMarking.NumberedWindowApplicationGraphTargets
open NumberedWindowAddressApplication NumberedWindowArithmeticScalarTargets
open NumberedWindowArithmeticClassAddress NumberedWindowArithmeticLeastClass
open NumberedWindowSimulationData NumberedWindowExternalApplication NumberedWindowPathWitnessTargets

/-- At an actual arrow-class address, all graph successes use an actual
argument class at the same context and the original domain type. -/
def ExactClassApplicationGraph : Prop :=
  ∀ S K Γ σ τ (hk : DecisionSourceUniverse.Closed K)
    (q : Class S K (finiteC Γ) (.arrow σ τ)) i,
    ActualCodeAt S K Γ (.arrow σ τ) i q →
    ∀ argument value,
      graph (fixed S K) (encodeAddress ⟨Γ,.arrow σ τ,i⟩) argument value = true ↔
        ∃ (j : Nat) (u : Class S K (finiteC Γ) σ) (k : Nat),
          argument = encodeAddress ⟨Γ,σ,j⟩ ∧
          ActualCodeAt S K Γ σ j u ∧
          value = encodeAddress ⟨Γ,τ,k⟩ ∧
          ActualCodeAt S K Γ τ k (appClass hk q u)

end LogicLineages.PersistentMarking.NumberedWindowApplicationGraphTargets
