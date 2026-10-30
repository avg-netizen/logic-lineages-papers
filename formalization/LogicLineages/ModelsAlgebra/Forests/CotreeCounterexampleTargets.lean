module

public import LogicLineages.ModelsAlgebra.Forests.CotreeCounterexampleDefinitions

/-! Bounded concrete counterexample to one literal path-containment transfer
clause, not a disproof of Carter's decision theorem. All cotree validity,
leaf enumeration, LCA uniqueness and actual graph interpretations are paid. -/
@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.Targets

open CotreeCounterexample

def ConcreteCotreesValid : Prop :=
  ValidCotree sourceCotree ∧ ValidCotree hostCotree ∧
  (∀ x y, ∃! z, IsLCA sourceCotree x y z) ∧
  (∀ x y, ∃! z, IsLCA hostCotree x y z)

def ConcreteCotreeLeavesExact : Prop :=
  Function.Injective sourceLeaves ∧
  (∀ v, (∃ i, sourceLeaves i = v) ↔ sourceCotree.label v = .leaf) ∧
  Function.Injective hostLeaves ∧
  (∀ v, (∃ i, hostLeaves i = v) ↔ hostCotree.label v = .leaf)

def ConcreteCotreeGraphsExact : Prop :=
  evaluatedGraph sourceCotree sourceLeaves = ⊥ ∧
  evaluatedGraph hostCotree hostLeaves = isolatedPathGraph ∧
  (∀ i j, (evaluatedGraph sourceCotree sourceLeaves).Adj i j ↔
    i ≠ j ∧ joinLCA sourceCotree (sourceLeaves i) (sourceLeaves j)) ∧
  (∀ i j, (evaluatedGraph hostCotree hostLeaves).Adj i j ↔
    i ≠ j ∧ joinLCA hostCotree (hostLeaves i) (hostLeaves j))

def ConcreteCotreePathObstruction : Prop :=
  ¬ Nonempty (PathCotreeEmbedding sourceCotree hostCotree)

def LiteralCotreeTransferCounterexample : Prop :=
  ValidCotree sourceCotree ∧ ValidCotree hostCotree ∧
  Nonempty ((evaluatedGraph sourceCotree sourceLeaves) ↪g
    (evaluatedGraph hostCotree hostLeaves)) ∧
  ¬ Nonempty (PathCotreeEmbedding sourceCotree hostCotree)

end LogicLineages.ModelsAlgebra.Forests.Targets
