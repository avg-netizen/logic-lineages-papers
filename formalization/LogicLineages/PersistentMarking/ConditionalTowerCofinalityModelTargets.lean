module

public import LogicLineages.PersistentMarking.ConditionalTowerCofinalityTargets
public import Mathlib.Data.ENat.Basic

@[expose] public section

namespace LogicLineages.PersistentMarking.ConditionalTowerCofinality

/-- A toy model of the collapse data, used only to show that the hypothesis
bundle `TowerHypotheses` is consistent. Index and value order are both
`ENat` (`ℕ` with a top element). The tower is `a n = n`, the endpoint is `⊤`,
every norm is `0`, the critical values are the positive ones, and the
collapse is the successor (`⊤ + 1 = ⊤`). This is NOT the collapse of Paper 16;
it is a non-vacuity witness. -/
def toyModel : CollapseData ENat ENat where
  psi ξ := ξ + 1
  norm _ := 0
  critical θ := 0 < θ
  one := 0
  endpoint := ⊤
  a n := (n : ENat)

/-- The toy model satisfies every hypothesis of the bundle. -/
def ToyModelSatisfiesHypotheses : Prop :=
  TowerHypotheses toyModel

/-- The hypothesis bundle of the conditional tower-cofinality theorems is
consistent: some concrete collapse data satisfies it. -/
def TowerHypothesesConsistent : Prop :=
  ∃ D : CollapseData ENat ENat, TowerHypotheses D

/-- Sanity check, proved directly in the model: the tower values have a
least upper bound (so the `IsLUB` premise of the conditional theorems is
satisfiable too), it is `⊤`, and it is the collapse at the endpoint. -/
def ToyModelConclusion : Prop :=
  IsLUB (Set.range (fun n => toyModel.psi (toyModel.a n))) (⊤ : ENat) ∧
    toyModel.psi toyModel.endpoint = (⊤ : ENat)

/-- Sanity check, obtained by instantiating the conditional theorem at the
model: every least upper bound of the tower values is the collapse at the
endpoint. -/
def ToyModelConditionalInstance : Prop :=
  ∀ θ : ENat, IsLUB (Set.range (fun n => toyModel.psi (toyModel.a n))) θ →
    θ = toyModel.psi toyModel.endpoint

end LogicLineages.PersistentMarking.ConditionalTowerCofinality
