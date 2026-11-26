module

public import LogicLineages.PersistentMarking.ConditionalTowerCofinalityTargets

@[expose] public section

namespace LogicLineages.PersistentMarking.ConditionalCollapseUniqueness
open ConditionalTowerCofinality

universe u v

/-- The characterization (P) determines the collapse: on a well-founded
index order, two collapses with the same coefficient norm and the same
critical class that both satisfy (P) are the same function. So (P) is a
legitimate defining clause ("this particular collapse"), and any function
satisfying it is the collapse. Existence is not claimed here. -/
def CharacterizationDeterminesCollapse : Prop :=
  ∀ (I : Type u) (O : Type v) [LinearOrder I] [WellFoundedLT I] [LinearOrder O]
    (D D' : CollapseData I O), D.norm = D'.norm → D.critical = D'.critical →
    CharacterizationP D → CharacterizationP D' → D.psi = D'.psi

end LogicLineages.PersistentMarking.ConditionalCollapseUniqueness
