module
public import LogicLineages.OrdinalComparison.CollapseTargets
public import LogicLineages.OrdinalComparison.NormBalls
public import LogicLineages.OrdinalComparison.Control
public import Mathlib.Data.Finset.Lattice.Fold

@[expose] public section

/-!
# Construction of the source norm-controlled collapse

This is the literal finite-maximum definition on intrinsically normal
hereditary Cantor notations. The recursive calls use their actual ordinal
order, whose well-foundedness comes from Mathlib's ordinal interpretation.
The finite-ball implementation is checked against the independent universal
upper-bound specification in `CollapseTargets`.
-/

namespace LogicLineages.OrdinalComparison

open Vendor.R1

def predecessorSet (a : NONote) (budget : Nat) : Finset NONote :=
  (notationNormBall budget).filter (fun b => b < a)

theorem mem_predecessorSet (a b : NONote) (budget : Nat) :
    b ∈ predecessorSet a budget ↔
      b < a ∧ treeWeight b.1 ≤ budget := by
  simp only [predecessorSet, Finset.mem_filter]
  rw [notationNormBall_exact budget b]
  exact and_comm

/-- The full fixed-control collapse, not a supplied correctness interface. -/
def collapse (a : NONote) : Nat :=
  (predecessorSet a (Phi (treeWeight a.1))).attach.sup
    (fun b => collapse b.1 + 1)
termination_by a
decreasing_by
  exact ((mem_predecessorSet _ _ _).mp b.2).1

theorem collapse_eq (a : NONote) :
    collapse a =
      (predecessorSet a (Phi (treeWeight a.1))).attach.sup
        (fun b => collapse b.1 + 1) := by
  rw [collapse]

theorem collapse_controlled (a b : NONote) (hba : b < a)
    (hn : treeWeight b.1 ≤ Phi (treeWeight a.1)) :
    collapse b + 1 ≤ collapse a := by
  have hm : b ∈ predecessorSet a (Phi (treeWeight a.1)) :=
    (mem_predecessorSet _ _ _).mpr ⟨hba, hn⟩
  let s := predecessorSet a (Phi (treeWeight a.1))
  have hmem : (⟨b, hm⟩ : {x : NONote // x ∈ s}) ∈ s.attach :=
    Finset.mem_attach s ⟨b, hm⟩
  have hle : collapse b + 1 ≤ s.attach.sup (fun x => collapse x.1 + 1) :=
    Finset.le_sup (f := fun x : {x : NONote // x ∈ s} => collapse x.1 + 1) hmem
  exact hle.trans_eq (collapse_eq a).symm

theorem collapse_le_upper (a : NONote) (k : Nat)
    (hk : ∀ b : NONote, b < a →
      treeWeight b.1 ≤ Phi (treeWeight a.1) → collapse b + 1 ≤ k) :
    collapse a ≤ k := by
  rw [collapse_eq a]
  apply Finset.sup_le
  intro b _
  exact hk b.1 ((mem_predecessorSet _ _ _).mp b.2).1
    ((mem_predecessorSet _ _ _).mp b.2).2

/-- The independent source equation holds without any semantic supplier premise. -/
theorem collapse_specification : Targets.NormControlledCollapse collapse := by
  intro a
  exact ⟨fun b => collapse_controlled a b, collapse_le_upper a⟩

theorem collapse_specification_unique (c d : NONote → Nat)
    (hc : Targets.NormControlledCollapse c) (hd : Targets.NormControlledCollapse d) :
    c = d := by
  funext a
  induction a using NONote.lt_wf.induction with
  | h a ih =>
      apply Nat.le_antisymm
      · apply (hc a).2 (d a)
        intro b hb hn
        rw [ih b hb]
        exact (hd a).1 b hb hn
      · apply (hd a).2 (c a)
        intro b hb hn
        rw [← ih b hb]
        exact (hc a).1 b hb hn

theorem uniqueNormControlledCollapse : Targets.UniqueNormControlledCollapse :=
  ⟨collapse, collapse_specification,
    fun d hd => collapse_specification_unique d collapse hd collapse_specification⟩

@[simp] theorem norm_ofNat (n : Nat) : treeWeight (NONote.ofNat n).1 = n := by
  cases n <;> simp [NONote.ofNat, ONote.ofNat, treeWeight]

theorem below_ofNat {a : NONote} {n : Nat} (h : a < NONote.ofNat n) :
    ∃ k : Nat, k < n ∧ a = NONote.ofNat k := by
  have hr : a.1.repr < (n : Ordinal) := by
    change a.1.repr < (ONote.ofNat n).repr at h
    simpa only [ONote.repr_ofNat] using h
  obtain ⟨k, hk⟩ := Ordinal.eq_natCast_of_le_natCast hr.le
  have hkn : k < n := by
    have hh : (k : Ordinal) < (n : Ordinal) := hk ▸ hr
    exact_mod_cast hh
  refine ⟨k, hkn, ?_⟩
  apply Subtype.ext
  haveI : ONote.NF a.1 := a.2
  apply ONote.repr_inj.mp
  simpa only [NONote.ofNat, ONote.repr_ofNat] using hk

theorem ofNat_lt_ofNat {n m : Nat} (h : n < m) :
    NONote.ofNat n < NONote.ofNat m := by
  change (ONote.ofNat n).repr < (ONote.ofNat m).repr
  simpa only [ONote.repr_ofNat, Nat.cast_lt] using h

/-- Finite inputs have exactly their finite source value. -/
theorem collapse_ofNat (n : Nat) : collapse (NONote.ofNat n) = n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      apply Nat.le_antisymm
      · apply collapse_le_upper
        intro b hb _
        obtain ⟨k, hk, rfl⟩ := below_ofNat hb
        rw [ih k hk]
        omega
      · cases n with
        | zero => exact Nat.zero_le _
        | succ n =>
            have hn : treeWeight (NONote.ofNat n).1 ≤
                Phi (treeWeight (NONote.ofNat (n + 1)).1) := by
              simp only [norm_ofNat]
              have hphi := self_lt_Phi (n + 1)
              omega
            have hl := collapse_controlled (NONote.ofNat (n + 1))
              (NONote.ofNat n) (ofNat_lt_ofNat (by omega)) hn
            rw [ih n (by omega)] at hl
            exact hl

theorem finiteCollapseValues : Targets.FiniteCollapseValues collapse := collapse_ofNat

theorem budget_lt_collapse_of_infinite (a : NONote)
    (hinf : Ordinal.omega0 ≤ a.1.repr) :
    Phi (treeWeight a.1) + 1 ≤ collapse a := by
  have hb : NONote.ofNat (Phi (treeWeight a.1)) < a := by
    change (ONote.ofNat (Phi (treeWeight a.1))).repr < a.1.repr
    rw [ONote.repr_ofNat]
    exact (Ordinal.natCast_lt_omega0 _).trans_le hinf
  have hn : treeWeight (NONote.ofNat (Phi (treeWeight a.1))).1 ≤
      Phi (treeWeight a.1) := (norm_ofNat (Phi (treeWeight a.1))).le
  simpa only [collapse_ofNat] using collapse_controlled a _ hb hn

theorem collapseDominatesNorm : Targets.CollapseDominatesNorm collapse := by
  intro a
  obtain ⟨n, hn⟩ | hinf := Ordinal.eq_natCast_or_omega0_le a.1.repr
  · have heq : a = NONote.ofNat n := by
      apply Subtype.ext
      haveI : ONote.NF a.1 := a.2
      apply ONote.repr_inj.mp
      simpa only [NONote.ofNat, ONote.repr_ofNat] using hn
    rw [heq, norm_ofNat, collapse_ofNat]
  · exact (self_lt_Phi (treeWeight a.1)).le.trans
      ((Nat.le_succ _).trans (budget_lt_collapse_of_infinite a hinf))

#print axioms collapse_specification
#print axioms uniqueNormControlledCollapse
#print axioms collapse_ofNat
#print axioms collapseDominatesNorm

end LogicLineages.OrdinalComparison
