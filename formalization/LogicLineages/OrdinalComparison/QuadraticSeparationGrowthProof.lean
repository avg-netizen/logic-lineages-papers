module
public import LogicLineages.OrdinalComparison.QuadraticSeparationTargets
public import LogicLineages.OrdinalComparison.ControlHierarchyGrowthProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.QuadraticSeparation.Proof

/-- The literal source bound pays both signed depths and all R extra steps. -/
theorem uniformQuadraticSeparation : Targets.UniformQuadraticSeparation := by
  intro w j k R h
  have hg := fullFastControlHierarchyGrowth.2.2 0 w (Nat.zero_le w)
  have hg' : 2 * Phi w ≤ Phi (w + 1) := by simpa using hg
  have hh : 2 * (Phi w / 2) ≤ Phi (w + 1) / 2 := by omega
  have hjlo : -(j.natAbs : Int) ≤ j := by omega
  have hjhi : j ≤ (j.natAbs : Int) := Int.le_natAbs
  have hklo : -(k.natAbs : Int) ≤ k := by omega
  have hkhi : k ≤ (k.natAbs : Int) := Int.le_natAbs
  have hdK : 0 < signedDepth k w := by
    dsimp [signedDepth]
    unfold Region at h
    omega
  have hdJ : 0 < signedDepth j (w + 1) := by
    dsimp [signedDepth]
    unfold Region at h
    omega
  have hd : (signedDepth k w).toNat + R ≤ (signedDepth j (w + 1)).toNat := by
    dsimp [signedDepth] at *
    unfold Region at h
    omega
  refine ⟨hdK, hdJ, ?_⟩
  change (Phi^[R]) ((Phi^[(signedDepth k w).toNat]) w) <
    (Phi^[(signedDepth j (w + 1)).toNat]) (w + 1)
  rw [← Function.iterate_add_apply]
  have hi : R + (signedDepth k w).toNat ≤ (signedDepth j (w + 1)).toNat := by omega
  exact ((Phi_strictMono.iterate (R + (signedDepth k w).toNat))
    (Nat.lt_succ_self w)).trans_le
      ((iterate_index_mono (fun x => (self_lt_Phi x).le) (w + 1)) hi)

end LogicLineages.OrdinalComparison.QuadraticSeparation.Proof
