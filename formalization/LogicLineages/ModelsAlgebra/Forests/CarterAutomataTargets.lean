module

public import LogicLineages.ModelsAlgebra.Forests.CarterAutomataDefinitions

/-! Bounded effective automata prerequisites only, not Carter's JEP algorithm.
The empty alphabet admits no tree; zero-state machines are treated without
nonempty assumptions. Symmetry is structural, not a correctness oracle. -/
@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.Targets

open CarterAutomata

def CarterReachableHeightExact : Prop :=
  ∀ k q (M : Automaton k q) n s,
    s ∈ reachable M n ↔ ∃ t, height t ≤ n ∧ run M t = s

def CarterReachableSaturation : Prop :=
  ∀ k q (M : Automaton k q), reachable M (q + 1) = reachable M q

def CarterAllRunsReachable : Prop :=
  ∀ k q (M : Automaton k q) t, run M t ∈ reachable M q

def CarterLanguageEmptiness : Prop :=
  ∀ k q (M : Automaton k q), languageEmpty M = true ↔ ¬ ∃ t, accepts M t

def CarterUnorderedRunInvariant : Prop :=
  ∀ k q (M : Automaton k q), Symmetric M →
    ∀ s t, UnorderedEquivalent s t → run M s = run M t

end LogicLineages.ModelsAlgebra.Forests.Targets
