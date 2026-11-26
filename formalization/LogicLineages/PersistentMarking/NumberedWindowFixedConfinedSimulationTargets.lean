import LogicLineages.PersistentMarking.NumberedWindowPositiveSimulationTargets

namespace LogicLineages.PersistentMarking.NumberedWindowFixedConfinedSimulationTargets
open NumberedWindowDomain NumberedWindowOrdinaryTranslation NumberedWindowSimulationData

/-- The ordinary translation is admitted in any supplied window containing
the literal source support, including when the term has no strict edge. -/
def OrdinaryQuoteInSuppliedWindow : Prop :=
  ∀ S K q τ, Spine.PaperTerm S q τ → Spine.Ordinary q →
    (∀ ρ ∈ TypeSupport.support q, ρ ∈ K) →
    ∃ Q, tr q = some Q ∧ InWindow S K Spine.EmptyContext τ Q

/-- A confined strict edge survives in the same supplied closed window.
The target's support follows from the original confinement premise. -/
def PositiveConfinedSimulationInSuppliedWindow : Prop :=
  ∀ S K s t, DecisionSourceUniverse.Closed K → (∀ ρ ∈ TypeSupport.support s, ρ ∈ K) →
    ConfinedPair.Strict S s t →
    ∃ Q T, tr s = some Q ∧ tr t = some T ∧
      ∃ hQ : InWindow S K Spine.EmptyContext s.type Q,
      ∃ hT : InWindow S K Spine.EmptyContext s.type T,
        RS S K Spine.EmptyContext s.type (classOf ⟨Q, hQ⟩) (classOf ⟨T, hT⟩)

end LogicLineages.PersistentMarking.NumberedWindowFixedConfinedSimulationTargets
