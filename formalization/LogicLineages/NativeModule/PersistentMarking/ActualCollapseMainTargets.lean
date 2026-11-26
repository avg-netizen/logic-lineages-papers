module

public import LogicLineages.NativeModule.PersistentMarking.ActualCollapseTargets
public import LogicLineages.NativeModule.PersistentMarking.ConditionalHeightEffectiveTargets
public import LogicLineages.NativeModule.PersistentMarking.ConditionalMain16UniformEffectiveCodedTargets

@[expose] public section

/-! The conditional Paper 16 statements re-closed on the actual collapse data
`veblenData fix pow w` (#1486), where `TowerHypotheses` is a theorem. Every statement is for
every solution of the arithmetic and ω equations; solutions exist unconditionally
(`exact_OrdinalArithmeticOrbits`, `exact_OrdinalOmegaOrbits`). -/

namespace LogicLineages.PersistentMarking.ActualCollapseMain
open Ordinal ActualOmegaTower ConditionalTowerCofinality OrdinalRealizationTargets
open OrdinalArithmeticOrbitTargets OrdinalOmegaOrbitTargets NativeTowerSequenceTargets
open ExternalOrdinalInterfaceTargets ConditionalHeightTargets ConditionalHeightEffectiveTargets
open ConditionalMain16UniformEffectiveCodedTargets ActualCollapse

/-- A solution of the paper's arithmetic and ω equations exists. -/
def SolutionExists : Prop :=
  ∃ (Z : CountableOrdinal) (s : CountableOrdinal → CountableOrdinal)
    (add mul : CountableOrdinal → CountableOrdinal → CountableOrdinal)
    (w one : CountableOrdinal) (pow : CountableOrdinal → CountableOrdinal)
    (fix : (CountableOrdinal → CountableOrdinal) → CountableOrdinal → CountableOrdinal),
    OrdinalArithmeticEquations Z s add mul ∧ OmegaArithmeticEquations Z s mul w one pow fix

/-- `lem:tower-cofinality` on the actual data: the supremum is the endpoint value outright, and
`BH` under the endpoint identification alone. -/
def ActualTowerCofinality : Prop :=
  ∀ (Z : CountableOrdinal) (s : CountableOrdinal → CountableOrdinal)
    (add mul : CountableOrdinal → CountableOrdinal → CountableOrdinal)
    (w one : CountableOrdinal) (pow : CountableOrdinal → CountableOrdinal)
    (fix : (CountableOrdinal → CountableOrdinal) → CountableOrdinal → CountableOrdinal),
    OrdinalArithmeticEquations Z s add mul → OmegaArithmeticEquations Z s mul w one pow fix →
    (⨆ n, (veblenData fix pow w).psi (actualArgument n)) = (veblenData fix pow w).psi actualEndpoint ∧
    ∀ BH : Ordinal.{0}, BHIdentification (veblenData fix pow w) BH →
      (⨆ n, (veblenData fix pow w).psi (actualArgument n)) = BH

/-- `thm:height` (effective form, #1470) on the actual data. -/
def ActualHeightEffective : Prop :=
  ∀ (Z : CountableOrdinal) (s : CountableOrdinal → CountableOrdinal)
    (add mul : CountableOrdinal → CountableOrdinal → CountableOrdinal)
    (w one : CountableOrdinal) (pow : CountableOrdinal → CountableOrdinal)
    (fix : (CountableOrdinal → CountableOrdinal) → CountableOrdinal → CountableOrdinal),
    OrdinalArithmeticEquations Z s add mul → OmegaArithmeticEquations Z s mul w one pow fix →
    ∀ BH : Ordinal.{0}, Calibration (veblenData fix pow w) → BHIdentification (veblenData fix pow w) BH →
      UpperBound BH → HeightIsBHEffective BH

/-- Paper 16 `thm:main`, uniform coded-effective form (#1477), on the actual data: four hypotheses. -/
def ActualMain16 : Prop :=
  ∀ (Z : CountableOrdinal) (s : CountableOrdinal → CountableOrdinal)
    (add mul : CountableOrdinal → CountableOrdinal → CountableOrdinal)
    (w one : CountableOrdinal) (pow : CountableOrdinal → CountableOrdinal)
    (fix : (CountableOrdinal → CountableOrdinal) → CountableOrdinal → CountableOrdinal),
    OrdinalArithmeticEquations Z s add mul → OmegaArithmeticEquations Z s mul w one pow fix →
    ∀ BH : Ordinal.{0},
      ExternalOrdinalInterfaceID1Targets.NormTheorem BH →
      ConditionalUpperUniformTargets.UniformAccessibility →
      Calibration (veblenData fix pow w) → BHIdentification (veblenData fix pow w) BH →
      Main16StatementCodedEffective BH

/-- The first two instances of the calibration `Δ_n' = ψ(a_n)` hold by definition:
`Δ_0' = ε_B = Γ` is the least critical value `ψ(0)`, and `Δ_1' = N_B(Γ)` is `ψ(1)`. -/
def CalibrationFirstInstances : Prop :=
  ∀ (Z : CountableOrdinal) (s : CountableOrdinal → CountableOrdinal)
    (add mul : CountableOrdinal → CountableOrdinal → CountableOrdinal)
    (w one : CountableOrdinal) (pow : CountableOrdinal → CountableOrdinal)
    (fix : (CountableOrdinal → CountableOrdinal) → CountableOrdinal → CountableOrdinal),
    OrdinalArithmeticEquations Z s add mul → OmegaArithmeticEquations Z s mul w one pow fix →
    (sequenceValue fix pow w 0).val = (veblenData fix pow w).psi (actualArgument 0) ∧
    (sequenceValue fix pow w 1).val = (veblenData fix pow w).psi (actualArgument 1)

end LogicLineages.PersistentMarking.ActualCollapseMain
