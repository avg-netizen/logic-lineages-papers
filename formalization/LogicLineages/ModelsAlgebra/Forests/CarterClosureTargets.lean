module

public import LogicLineages.ModelsAlgebra.Forests.CarterClosureDefinitions

/-! Exact Boolean closure, symmetry and language equivalence. These statements
concern only the explicit full-binary syntax, not source graph embeddings. -/
@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.Targets

open CarterAutomata

def CarterProductRun : Prop :=
  ∀ k q r mode (M : Automaton k q) (N : Automaton k r) t,
    finProdFinEquiv.symm (run (productMachine mode M N) t) = (run M t, run N t)

def CarterComplementLanguage : Prop :=
  ∀ k q (M : Automaton k q) t, accepts (complementMachine M) t ↔ ¬ accepts M t

def CarterIntersectionLanguage : Prop :=
  ∀ k q r (M : Automaton k q) (N : Automaton k r) t,
    accepts (intersectionMachine M N) t ↔ accepts M t ∧ accepts N t

def CarterUnionLanguage : Prop :=
  ∀ k q r (M : Automaton k q) (N : Automaton k r) t,
    accepts (unionMachine M N) t ↔ accepts M t ∨ accepts N t

def CarterDifferenceLanguage : Prop :=
  ∀ k q r (M : Automaton k q) (N : Automaton k r) t,
    accepts (symmetricDifferenceMachine M N) t ↔ ¬ (accepts M t ↔ accepts N t)

def CarterLanguageEquivalence : Prop :=
  ∀ k q r (M : Automaton k q) (N : Automaton k r),
    languageEquivalent M N = true ↔ ∀ t, accepts M t ↔ accepts N t

def CarterComplementSymmetric : Prop :=
  ∀ k q (M : Automaton k q), Symmetric M → Symmetric (complementMachine M)

def CarterProductSymmetric : Prop :=
  ∀ k q r mode (M : Automaton k q) (N : Automaton k r),
    Symmetric M → Symmetric N → Symmetric (productMachine mode M N)

end LogicLineages.ModelsAlgebra.Forests.Targets
