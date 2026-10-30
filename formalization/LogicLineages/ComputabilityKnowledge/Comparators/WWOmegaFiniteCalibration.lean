module

public import LogicLineages.ComputabilityKnowledge.WWOmegaFiniteCalibration

@[expose] public section

namespace LogicLineages.ComputabilityKnowledge.Comparators.WWOmegaFiniteCalibration

open LogicLineages.OrdinalComparison
open LogicLineages.ComputabilityKnowledge.WWOmegaFiniteCalibration

def ProductCalibration : Prop :=
  ∀ n : Nat, ordinalNaturalProduct Ordinal.omega0 (n : Ordinal.{0}) = Ordinal.omega0 * (n : Ordinal.{0})

def SumCalibration : Prop :=
  ∀ n g : Nat, ordinalNaturalSum (Ordinal.omega0 * (n : Ordinal.{0})) (g : Ordinal.{0}) =
    Ordinal.omega0 * (n : Ordinal.{0}) + (g : Ordinal.{0})

def NormCalibration : Prop :=
  ∀ n g : Nat, block n g < epsilonZero ∧ actualOrdinalNorm (block n g) = 2 * n + g

def CollapseCalibration : Prop :=
  ∀ n g : Nat, 2 * n + g ≤ actualCollapse (block n g) ∧ n ≤ actualCollapse (block n g)

def Target : Prop := ProductCalibration ∧ SumCalibration ∧ NormCalibration ∧ CollapseCalibration

end LogicLineages.ComputabilityKnowledge.Comparators.WWOmegaFiniteCalibration
