module

public import LogicLineages.ModelsAlgebra.Forests.CarterWitnessDefinitions

/-! Constructive finite-state representative and language witness contracts. -/
@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.Targets

open CarterAutomata

def CarterTreeEnumerationExact : Prop :=
  ∀ k n (t : BinaryLabelTree k), t ∈ treesUpTo k n ↔ height t ≤ n

def CarterTreeSizeBound : Prop :=
  ∀ k (t : BinaryLabelTree k), vertexCount t < 2 ^ height t

def CarterBoundedRunRepresentative : Prop :=
  ∀ k q (M : Automaton k q) t,
    ∃ s ∈ treesUpTo k q, run M s = run M t ∧ vertexCount s < 2 ^ q

def CarterAcceptedWitnessSound : Prop :=
  ∀ k q (M : Automaton k q) t, acceptedWitness M = some t →
    t ∈ treesUpTo k q ∧ accepts M t

def CarterAcceptedWitnessComplete : Prop :=
  ∀ k q (M : Automaton k q), acceptedWitness M = none ↔ languageEmpty M = true

end LogicLineages.ModelsAlgebra.Forests.Targets
