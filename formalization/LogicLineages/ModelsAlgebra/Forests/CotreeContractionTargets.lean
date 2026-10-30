module

public import LogicLineages.ModelsAlgebra.Forests.CotreeContractionDefinitions

/-! Concrete obstruction to the reverse transfer under unrestricted
parent-label contraction. No assertion about other label/embedding conventions
or the final JEP decision theorem is made. -/
@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.Targets

open CotreeCounterexample

def ContractionCotreeValid : Prop :=
  ValidCotree contractionHost ∧
  (∀ x y, ∃! z, IsLCA contractionHost x y z) ∧
  Function.Injective contractionLeaves ∧
  (∀ v, (∃ i, contractionLeaves i = v) ↔ contractionHost.label v = .leaf)

def ContractionCotreeGraphExact : Prop :=
  evaluatedGraph contractionHost contractionLeaves = isolatedEdgeGraph ∧
  (∀ i j, (evaluatedGraph contractionHost contractionLeaves).Adj i j ↔
    i ≠ j ∧ joinLCA contractionHost (contractionLeaves i) (contractionLeaves j))

def ConcreteParentLabelContraction : Prop :=
  ParentLabelContraction contractionHost sourceCotree 0 2 contractionQuotient

def ContractionGraphNonembedding : Prop :=
  ¬ Nonempty ((evaluatedGraph sourceCotree sourceLeaves) ↪g
    (evaluatedGraph contractionHost contractionLeaves))

def LiteralContractionTransferCounterexample : Prop :=
  ValidCotree contractionHost ∧ ValidCotree sourceCotree ∧
  ParentLabelContraction contractionHost sourceCotree 0 2 contractionQuotient ∧
  ¬ Nonempty ((evaluatedGraph sourceCotree sourceLeaves) ↪g
    (evaluatedGraph contractionHost contractionLeaves))

end LogicLineages.ModelsAlgebra.Forests.Targets
