module

public import LogicLineages.NativeModule.PersistentMarking.ActualCalibrationMonotoneProof

@[expose] public section

/-! Layer 2: `N_B^β(Γ_0) ≤ N_B^((ω+1)+β)(0)`, from `Γ_0 = N_B(ω) ≤ N_B(N_B^ω(0)) = N_B^(ω+1)(0)`,
start-monotonicity and composition. -/

namespace LogicLineages.PersistentMarking.ActualCalibration
open Ordinal Cardinal ActualOmegaTower OrdinalRealizationTargets OrdinalNativeOrbitProof
open OrdinalArithmeticOrbitTargets OrdinalOmegaOrbitTargets NativeTowerTargets NativeTowerSequenceTargets
open ActualCollapse
open scoped Ordinal

theorem orbitComparison : OrbitComparison := by
  intro Z s add mul w one pow fix h1 h2 β γ hγ
  let N := veblenValue fix pow
  have mi : MonoInfl N := veblen_monoInfl h1 h2
  have hω1 : (ω : Ordinal.{0}) + 1 < ω₁ :=
    (isSuccLimit_omega 1).add_one_lt omega0_lt_omega_one
  let ωc := mkCountable ω omega0_lt_omega_one
  let ω1c := mkCountable (ω + 1) hω1
  have start : (baseValue fix pow w).val ≤ (orbit .base N zeroValue ω1c).val := by
    rw [orbit_succ N zeroValue ωc ω1c rfl]
    show (N w).val ≤ _
    refine mi.1 _ _ ?_
    rw [h2.1]
    exact orbit_id_le N zeroValue mi.2 ωc
  exact (orbit_start_mono N mi.1 _ _ start β).trans (orbit_compose_le N mi zeroValue ω1c β γ hγ)

end LogicLineages.PersistentMarking.ActualCalibration
