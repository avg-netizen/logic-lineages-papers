module
public import LogicLineages.StandardControlCurrent.InverseCutTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovInverseProof
public import Mathlib.Data.Nat.ModEq
@[expose] public section
namespace LogicLineages.StandardControlCurrent.InverseCutProof
open OrdinalComparison LayeredComparison.SnyatkovInverse InverseCut

theorem lowerExact (g inv : Nat → Nat) (hg : StrictMono g) (hi : FloorGraph g inv)
    (lo x : Nat) : lowerIndex g inv lo ≤ x ↔ lo ≤ g x := by
  unfold lowerIndex
  split
  · rename_i h
    exact ⟨fun _ => h.trans (hg.monotone (Nat.zero_le x)),fun _ => Nat.zero_le x⟩
  · rename_i h
    have hp : 0 < lo := by omega
    have hf := (hi (lo-1) (inv (lo-1))).mp rfl
    have hl : g (inv (lo-1)) ≤ lo-1 := by
      rcases hf.1 with hz | hl
      · rw [hz]; omega
      · exact hl
    constructor
    · intro hx
      have hm := hg.monotone hx
      omega
    · intro hx
      by_contra hn
      have hm := hg.monotone (show x ≤ inv (lo-1) by omega)
      omega

theorem leastResidue : InverseCutTargets.LeastResidue := by
  intro a m r hm hr
  have ha := Nat.mod_lt a hm
  have hsum : a%m + (r+m-a%m) = r+m := by omega
  have hres : residueNext a m r % m = r := by
    unfold residueNext
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, hsum]
    simp [Nat.mod_eq_of_lt hr]
  have hb : residueNext a m r < a+m := by
    have hd := Nat.mod_lt (r+m-a%m) hm
    unfold residueNext
    omega
  refine ⟨by unfold residueNext; omega,hres,?_⟩
  intro x hx hxr
  have he : Nat.ModEq m (residueNext a m r) x := by
    change residueNext a m r % m = x % m
    rw [hres,hxr]
  exact he.le_of_lt_add (by omega)

theorem cutExact (g inv : Nat → Nat) (hg : StrictMono g)
    (hl : ∀ lo x, lowerIndex g inv lo ≤ x ↔ lo ≤ g x) (p : Input) :
    answer g inv p = true ↔ 0 < p.2.2.2.2.1 ∧ p.2.2.2.2.2 < p.2.2.2.2.1 ∧ Cut g p := by
  simp only [answer,decide_eq_true_eq]
  constructor
  · rintro ⟨hm,hr,hb,hh⟩
    have hc := leastResidue (max p.1 (lowerIndex g inv p.2.2.1)) _ _ hm hr
    refine ⟨hm,hr,candidate g inv p,?_,hb,?_,hh,hc.2.1⟩
    · exact (Nat.le_max_left _ _).trans hc.1
    · exact (hl _ _).mp ((Nat.le_max_right _ _).trans hc.1)
  · rintro ⟨hm,hr,x,ha,hb,hlo,hhi,hres⟩
    have hc := leastResidue (max p.1 (lowerIndex g inv p.2.2.1)) _ _ hm hr
    have hcx : candidate g inv p ≤ x := hc.2.2 x (max_le ha ((hl _ _).mpr hlo)) hres
    exact ⟨hm,hr,hcx.trans hb,(hg.monotone hcx).trans hhi⟩

theorem lowerCuts : InverseCutTargets.ActualLowerCuts := by
  intro lo x
  exact ⟨lowerExact Phi phiInverse Phi_strictMono Proof.exactOriginalGraphs.1 lo x,
    lowerExact FixedSeedControlResidue.H hyperInverse FixedSeedControlResidue.Proof.h_strictMono
      Proof.exactOriginalGraphs.2 lo x⟩

theorem elimination : InverseCutTargets.ActualCutElimination := by
  intro p
  exact ⟨cutExact Phi phiInverse Phi_strictMono (fun lo x => (lowerCuts lo x).1) p,
    cutExact FixedSeedControlResidue.H hyperInverse FixedSeedControlResidue.Proof.h_strictMono
      (fun lo x => (lowerCuts lo x).2) p⟩
end LogicLineages.StandardControlCurrent.InverseCutProof
