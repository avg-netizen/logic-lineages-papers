module
public import LogicLineages.CartierObserverCurrent.LinkedBoundaryParityTargets
public import LogicLineages.OrdinalComparison.OmegaBlockNumericalProof
public import LogicLineages.OrdinalComparison.BinaryPartitionSeriesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.CartierObserverCurrent.LinkedBoundaryParity
open LogicLineages.OrdinalComparison

theorem actualBoundaryParity : Targets.ActualBoundaryParity := by
  intro v hv
  let u := Phi v
  let B := Phi u
  let C := Phi (u + 1)
  let e := u - 4
  let d := B - u + 3
  have hu : 4 ≤ u := hv.trans (self_lt_Phi v).le
  have hBu : u < B := self_lt_Phi u
  have hCu : u < C := (Nat.lt_succ_self u).trans (self_lt_Phi (u + 1))
  have hB : 16 ≤ B := by
    calc
      16 = 2 ^ 4 := by decide
      _ ≤ 2 ^ (u + 100) := Nat.pow_le_pow_right (by decide) (by omega)
      _ ≤ B := two_pow_shift_le_Phi u
  have hd : 0 < d := by dsimp [d]; omega
  have he : e + 4 = u := by dsimp [e]; omega
  have hdim : d + e + 1 = B := by dsimp [d,e]; omega
  have hdiff : Phi u - e - 1 = d := by dsimp [d,e,B] at *; omega
  have h := actualNumericalOmegaBlock e u 2 (by omega) (by decide) hB (by omega)
  have hp : actualOmegaCopyCount e u % 2 = (1 + restrictedPartitionCount d (C - e)) % 2 := by
    have hh := h.1
    rw [hdiff] at hh
    exact hh
  have heC : e ≤ C := by omega
  refine ⟨hd, he, hdim, heC, hp, ?_⟩
  rw [←actualBinaryPartitionSeriesQuotient d]
  simpa only [actualBinaryPartitionSeries, PowerSeries.coeff_mk, ZMod.val_natCast,
    Nat.add_mod, Nat.mod_mod] using hp

#audit_namespace LogicLineages.CartierObserverCurrent.LinkedBoundaryParity
end LogicLineages.CartierObserverCurrent.LinkedBoundaryParity
