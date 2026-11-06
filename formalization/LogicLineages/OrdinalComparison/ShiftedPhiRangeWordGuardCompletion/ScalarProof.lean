module
public import LogicLineages.OrdinalComparison.ShiftedPhiRangeWordGuardCompletion.Targets
public import LogicLineages.OrdinalComparison.ControlHierarchyGrowthProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.ShiftedPhiRangeWordGuardCompletion.Proof

/-- A genuine integer input step creates the entire requested additive gap. -/
theorem phi_gap (K u v : Nat) (hK : K ≤ u) (huv : u < v) : Phi u+K < Phi v := by
  have hg := fullFastControlHierarchyGrowth.2.2 0 u (Nat.zero_le u)
  have hd : 2*Phi u ≤ Phi (u+1) := by simpa using hg
  have hm := Phi_strictMono.monotone (show u+1 ≤ v by omega)
  have hs := self_lt_Phi u
  omega

theorem shiftedPhiOrder : Targets.ShiftedPhiOrder := by
  intro j k u v hu hv
  have hj : -(j.natAbs : Int) ≤ j := by omega
  have hk : -(k.natAbs : Int) ≤ k := by omega
  have hj' : j ≤ (j.natAbs : Int) := Int.le_natAbs
  have hk' : k ≤ (k.natAbs : Int) := Int.le_natAbs
  have hsu := self_lt_Phi u
  have hsv := self_lt_Phi v
  have hK : j.natAbs+k.natAbs ≤ u := by unfold scalarTail at hu; omega
  have hK' : j.natAbs+k.natAbs ≤ v := by unfold scalarTail at hv; omega
  have hpL : 0 < (Phi u : Int)+j := by omega
  have hpR : 0 < (Phi v : Int)+k := by omega
  refine ⟨hpL,hpR,?_⟩
  rcases lt_trichotomy u v with huv | rfl | hvu
  · have hg := phi_gap (j.natAbs+k.natAbs) u v hK huv
    dsimp [PreimageLexLT]
    omega
  · dsimp [PreimageLexLT]
    omega
  · have hg := phi_gap (j.natAbs+k.natAbs) v u hK' hvu
    dsimp [PreimageLexLT]
    omega

end LogicLineages.OrdinalComparison.ShiftedPhiRangeWordGuardCompletion.Proof
