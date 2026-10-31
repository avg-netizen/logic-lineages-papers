module
public import LogicLineages.ModelsAlgebra.Forests.RankedPruneAlgorithmDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.RankedPruneAlgorithm.Targets
open RankedParse

/-- The executable deletion procedure returns no parse exactly for the empty selection. -/
def NoneExact : Prop :=
  ∀ (t : Term) (B : Leaf t → Bool), prune t B = none ↔ ∀ x, B x = false

/-- Every actual output has the exact selected induced graph and the exact
ranked homeomorphic relation, with no replacement by a chosen parse. -/
def SomeExact : Prop :=
  ∀ (t : Term) (B : Leaf t → Bool) (s : Term), prune t B = some s →
    Homeomorphic s t ∧ ∃ f : InducedMap s t,
      ∀ y, (∃ x, f.map x = y) ↔ B y = true

end LogicLineages.ModelsAlgebra.Forests.RankedPruneAlgorithm.Targets
