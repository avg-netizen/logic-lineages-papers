module
public import LogicLineages.OrdinalComparison.SourceGammaCollisionTargets
public import LogicLineages.OrdinalComparison.ParametricSourceEraserProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceGammaCollision.Proof

theorem phi_gap_eight (n : Nat) : 4*Phi n+8<Phi (n+1) := by
  have ha := four_le_Phi n
  have h := four_mul_add_four_lt_two_pow_succ ha
  have hh : 4*Phi n+8<2^(Phi n+2) := by
    rw [show Phi n+2=(Phi n+1)+1 by omega,Nat.pow_succ]
    omega
  have he : Phi n+2 ≤ 2^Phi n := by
    have ht := PerturbedControl.Proof.twice_le_pow (Phi n)
    omega
  exact (hh.trans_le (Nat.pow_le_pow_right (by decide) he)).trans_le (Phi_double_tower_gap n)

theorem g_calibration (b n : Nat) : g b n=SourceMachineControlNonperiodicity.gamma b (n+2)+1 :=
  (ParametricCoefficientOne.Proof.actualGammaCoefficientOne b).2.2 n

theorem g_strictMono (b : Nat) : StrictMono (g b) := by
  intro x y hxy
  rw [g_calibration,g_calibration]
  have h := (ParametricCoefficientOne.Proof.actualGammaCoefficientOne b).1 (by omega : x+2<y+2)
  omega

theorem g_positive (b n : Nat) : 0<g b n := by
  rw [g_calibration]
  omega

theorem g_four_gap (b n : Nat) : 4*g b n<g b (n+1) := by
  rw [g_calibration,g_calibration]
  have h := PerturbedControl.Proof.bounds b SourceBlankMachineSimulation.boundedH (n+2)
  have h' := PerturbedControl.Proof.bounds b SourceBlankMachineSimulation.boundedH (n+1+2)
  change Phi (n+2) ≤ SourceMachineControlNonperiodicity.gamma b (n+2) ∧
    SourceMachineControlNonperiodicity.gamma b (n+2) ≤ Phi (n+2)+1 at h
  change Phi (n+1+2) ≤ SourceMachineControlNonperiodicity.gamma b (n+1+2) ∧
    SourceMachineControlNonperiodicity.gamma b (n+1+2) ≤ Phi (n+1+2)+1 at h'
  have hg := phi_gap_eight (n+2)
  have he : n+2+1=n+1+2 := by omega
  rw [he] at hg
  omega

theorem g_four_lt (b a c : Nat) (h : a<c) : 4*g b a<g b c :=
  (g_four_gap b a).trans_le ((g_strictMono b).monotone (Nat.succ_le_of_lt h))

theorem actualControlGap : Targets.ActualControlGap :=
  fun b => ⟨g_calibration b,g_strictMono b,g_positive b,g_four_gap b⟩
end LogicLineages.OrdinalComparison.Source.SourceGammaCollision.Proof
