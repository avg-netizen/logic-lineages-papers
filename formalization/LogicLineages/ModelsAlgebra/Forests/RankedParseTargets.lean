module
public import LogicLineages.ModelsAlgebra.Forests.RankedParseDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.RankedParse.Targets

/-- First assertion of repaired paper 03, Lemma `lem:parse-pruning`. -/
def HomeomorphicInduced : Prop :=
  ∀ s t, Homeomorphic s t → Nonempty (InducedMap s t)

/-- Second assertion: every nonempty set of leaf occurrences is precisely the
image of an induced embedding of a smaller ranked parse. Injectivity and
adjacency equivalence identify its graph with the induced restriction. -/
def ExactPruning : Prop :=
  ∀ (t : Term) (B : Leaf t → Prop), (∃ x, B x) →
    ∃ s, Homeomorphic s t ∧ ∃ f : InducedMap s t,
      ∀ y, (∃ x, f.map x = y) ↔ B y

end LogicLineages.ModelsAlgebra.Forests.RankedParse.Targets
