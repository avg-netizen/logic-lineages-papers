module
public import LogicLineages.OrdinalComparison.ParametricSourceEraserDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceGammaCollision
/-- The actual coefficient-one ordinal collapse for the chosen Gamma. -/
noncomputable def g (b n : Nat) : Nat :=
  ParametricCoefficientOne.coefficientOne (SourceMachineControlNonperiodicity.gamma b) n
noncomputable def leftValue (b p q : Nat) : Nat :=
  g b (3*g b (3*p+p+2)+g b (3*q+q+2)+2)
noncomputable def rightValue (b p q : Nat) : Nat :=
  g b (3*g b (3*p+q+2)+g b (3*q+p+2)+2)
end LogicLineages.OrdinalComparison.Source.SourceGammaCollision
