module
public import LogicLineages.ModelsAlgebra.Forests.CotreeGrammarProductionDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreeGrammarProduction.Targets
open CotreeGrammarOpen CotreeGrammarRotation

def BinaryFactorization : Prop := ∀ (Q : Type) [DecidableEq Q] (δ : Q → Q → Q)
  q (t : Tree δ q) r s, 0 < (counts t).binary (r,s) ↔
    ∃ (C : Context δ q (δ r s)) (l : Tree δ r) (u : Tree δ s), plug C (.branch l u) = t

def ContainsFactorization : Prop := ∀ (Q : Type) (δ : Q → Q → Q)
  r q (t : Tree δ r) (u : Tree δ q),
  Contains u t ↔ ∃ C : Context δ r q, plug C u = t

/-- The chosen exact production subtree is preserved in both branches. -/
def ExactContextDichotomy : Prop := ∀ (Q : Type) (δ : Q → Q → Q)
  r x (C : Context δ r x) y (u : Tree δ y), Contains u (plug C (.hole x)) →
  (∃ (P : Context δ r y) (S : Context δ y x), C = compose P S ∧ u = plug S (.hole x)) ∨
  ∃ D : TwoContext δ r y x, ∀ v : Tree δ x, plug C v = fill D u v

/-- Actual rank-decreasing cycle rotation at a specified positive production;
both on-path and off-path cases are paid, with all production multiplicities unchanged. -/
def CycleRotateProduction : Prop := ∀ (Q : Type) [DecidableEq Q] (δ : Q → Q → Q)
  x (t : Tree δ x) r s, holes t = [x] → 0 < (counts t).binary (r,s) →
  (r = x ∨ s = x) → ∃ u : Tree δ (δ r s), holes u = [δ r s] ∧ counts u = counts t

end LogicLineages.ModelsAlgebra.Forests.CotreeGrammarProduction.Targets
