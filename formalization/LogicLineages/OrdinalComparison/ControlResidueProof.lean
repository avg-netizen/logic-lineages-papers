module
public import LogicLineages.OrdinalComparison.ControlTowerResidueProof
public import LogicLineages.OrdinalComparison.ControlHierarchyGrowthProof

@[expose] public section

namespace LogicLineages.OrdinalComparison

theorem fastControlResidueRange : Targets.FastControlResidueRange := by
  intro m hm
  exact Nat.mod_lt _ hm

theorem fastControlResiduePrimitiveRecursive : Targets.FastControlResiduePrimitiveRecursive :=
  Primrec.nat_mod.comp (fixed_fastControl_primrec 1) Primrec.id

private theorem positive_level_residue (m : Nat) (hm : 0 < m) (j : Nat) :
    ∀ n : Nat, m ≤ n → Nat.ModEq m (fastControl (j + 1) n) (fastControlResidue m) := by
  induction j with
  | zero =>
    intro n hn
    have ht := exponentTowerResidueStability m hm n m (n + 1) (m + 1) hn le_rfl
      (by omega) (by omega)
    change Nat.ModEq m (fastControl 1 n) (fastControl 1 m) at ht
    apply ht.trans
    simp only [Nat.ModEq, fastControlResidue, Nat.mod_mod]
  | succ j ih =>
    intro n hn
    let v := ((fastControl (j + 1))^[n]) n
    have hnv : n ≤ v := iterate_self_le (fun z => (self_lt_fastControl (j + 1) z).le) n n
    change Nat.ModEq m (((fastControl (j + 1))^[n + 1]) n) (fastControlResidue m)
    rw [Function.iterate_succ_apply']
    exact ih v (hn.trans hnv)

theorem fastControlConstantResidues : Targets.FastControlConstantResidues := by
  intro m hm j n hj hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  exact positive_level_residue m hm k n hn

theorem phiShiftedConstantResidues : Targets.PhiShiftedConstantResidues := by
  intro m hm n hn
  exact fastControlConstantResidues m hm 5 (n + 100) (by decide) (by omega)

theorem fastControlDoubleExponentResidueEnvelope : Targets.FastControlDoubleExponentResidueEnvelope := by
  intro m hm s j hs hj hmod
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  have hk : 1 ≤ k := by omega
  let v := ((fastControl k)^[s]) s
  have hiter : fastControl k s ≤ v := by
    have h := iterate_index_mono (fun z => (self_lt_fastControl k z).le) s hs
    simpa only [Function.iterate_one, id_eq] using h
  have hlarge : 2 ^ (2 ^ s) ≤ v := (two_tower_le_fastControl hk hs).trans hiter
  change Nat.ModEq m (((fastControl k)^[s + 1]) s) (fastControlResidue m)
  rw [Function.iterate_succ_apply']
  exact fastControlConstantResidues m hm k v hk (hmod.trans hlarge)

theorem phiNextInputResidueEnvelope : Targets.PhiNextInputResidueEnvelope := by
  intro m hm u hmod
  let n := u + 100
  let v := ((fastControl 4)^[n + 1]) (n + 1)
  have hv : Phi u < v := by
    change ((fastControl 4)^[n + 1]) n < ((fastControl 4)^[n + 1]) (n + 1)
    exact (fastControl_strictMono 4).iterate (n + 1) (Nat.lt_succ_self n)
  have hvpos : 1 ≤ v := by omega
  have hdouble : 2 ^ (2 ^ Phi u) ≤ 2 ^ (2 ^ v) :=
    Nat.pow_le_pow_right (by decide) (Nat.pow_le_pow_right (by decide) hv.le)
  have hres := fastControlDoubleExponentResidueEnvelope m hm v 4 hvpos (by decide)
    (hmod.trans hdouble)
  have hinput : Phi (u + 1) = fastControl 4 v := by
    change fastControl 5 (u + 1 + 100) = fastControl 4 v
    rw [show u + 1 + 100 = n + 1 by dsimp [n]]
    change ((fastControl 4)^[n + 1 + 1]) (n + 1) = fastControl 4 v
    rw [Function.iterate_succ_apply']
  rw [hinput]
  exact hres

theorem fullFastControlConstantResidues : Targets.FullFastControlConstantResidues :=
  ⟨fastControlResidueRange, fastControlResiduePrimitiveRecursive,
    fastControlConstantResidues, phiShiftedConstantResidues,
    fastControlDoubleExponentResidueEnvelope, phiNextInputResidueEnvelope⟩

theorem fullUniformResidueEnvelopes : Targets.FullUniformResidueEnvelopes := by
  refine ⟨fastControlResidueRange, fastControlResiduePrimitiveRecursive, ?_,
    fastControlDoubleExponentResidueEnvelope, phiNextInputResidueEnvelope⟩
  intro m hm x hx
  exact phiShiftedConstantResidues m hm x (by omega)

end LogicLineages.OrdinalComparison
