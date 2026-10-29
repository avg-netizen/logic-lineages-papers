module
public import LogicLineages.OrdinalComparison.Targets
public import Mathlib.Data.Finset.Union

@[expose] public section

/-!
# Finite norm balls for hereditary Cantor notations

The norm is the source's additive expanded-tree norm, not binary syntax size.
This module enumerates raw hereditary notations of bounded norm and then
filters normal forms. The finite-ball supplier is proved, not assumed.

Paper mapping: foundations, Lemma `lem:finite-balls` (finiteness and effective
enumeration portion). Natural-sum norm additivity and source assignments are
separate unfinished targets.
-/

namespace LogicLineages.OrdinalComparison

open Vendor.R1

/-- One positive-coefficient monomial, with its coefficient stored minus one. -/
def rawNode (e t : ONote) (k : Nat) : ONote :=
  .oadd e ⟨k + 1, Nat.succ_pos k⟩ t

/-- A finite executable enumeration; the final filter enforces the exact norm. -/
def rawNormBall : Nat → Finset ONote
  | 0 => {0}
  | b + 1 =>
      ({0} ∪ (rawNormBall b).biUnion (fun e =>
        (rawNormBall b).biUnion (fun t =>
          (Finset.range (b + 1)).image (rawNode e t)))).filter
        (fun a => treeWeight a ≤ b + 1)

theorem treeWeight_eq_zero_iff (a : ONote) : treeWeight a = 0 ↔ a = 0 := by
  cases a with
  | zero => simp [treeWeight]
  | oadd e c t =>
      have hc : 0 < (c : Nat) := c.pos
      have hp : 0 < (c : Nat) * (1 + treeWeight e) :=
        Nat.mul_pos hc (by omega)
      simp only [treeWeight]
      constructor
      · intro h
        omega
      · intro h
        cases h

/-- Membership is exactly the norm bound, including nonnormal raw syntax. -/
theorem mem_rawNormBall (b : Nat) (a : ONote) :
    a ∈ rawNormBall b ↔ treeWeight a ≤ b := by
  induction b generalizing a with
  | zero =>
      simp only [rawNormBall, Finset.mem_singleton, Nat.le_zero]
      exact (treeWeight_eq_zero_iff a).symm
  | succ b ih =>
      constructor
      · intro ha
        exact (Finset.mem_filter.mp ha).2
      · intro ha
        apply Finset.mem_filter.mpr
        refine ⟨?_, ha⟩
        cases a with
        | zero => exact Finset.mem_union.mpr (Or.inl (by simp))
        | oadd e c t =>
            have hc : 1 ≤ (c : Nat) := Nat.succ_le_of_lt c.pos
            have hfactor : 1 ≤ 1 + treeWeight e := by omega
            have hprod : 1 + treeWeight e ≤ (c : Nat) * (1 + treeWeight e) := by
              simpa only [Nat.one_mul] using Nat.mul_le_mul_right (1 + treeWeight e) hc
            have hcoef : (c : Nat) ≤ (c : Nat) * (1 + treeWeight e) := by
              simpa only [Nat.mul_one] using Nat.mul_le_mul_left (c : Nat) hfactor
            have he : treeWeight e ≤ b := by
              simp only [treeWeight] at ha
              omega
            have ht : treeWeight t ≤ b := by
              simp only [treeWeight] at ha
              omega
            have hcb : (c : Nat) ≤ b + 1 := by
              simp only [treeWeight] at ha
              omega
            apply Finset.mem_union.mpr
            right
            apply Finset.mem_biUnion.mpr
            refine ⟨e, (ih e).mpr he, ?_⟩
            apply Finset.mem_biUnion.mpr
            refine ⟨t, (ih t).mpr ht, ?_⟩
            apply Finset.mem_image.mpr
            refine ⟨(c : Nat) - 1, Finset.mem_range.mpr (by omega), ?_⟩
            have hn : (⟨(c : Nat) - 1 + 1, Nat.succ_pos _⟩ : ℕ+) = c := by
              apply Subtype.ext
              change (c : Nat) - 1 + 1 = (c : Nat)
              exact Nat.sub_add_cancel hc
            simp only [rawNode, hn]

/-- Raw notation norm balls are finite sets, with a displayed finite enumeration. -/
theorem finite_rawNormBall (b : Nat) :
    Set.Finite {a : ONote | treeWeight a ≤ b} := by
  have heq : {a : ONote | treeWeight a ≤ b} = (rawNormBall b : Set ONote) := by
    ext a
    exact (mem_rawNormBall b a).symm
  rw [heq]
  exact (rawNormBall b).finite_toSet

/-- The normal-form sublist is executable because Mathlib decides normality. -/
def normalNormBall (b : Nat) : Finset ONote :=
  (rawNormBall b).filter ONote.NF

theorem mem_normalNormBall (b : Nat) (a : ONote) :
    a ∈ normalNormBall b ↔ ONote.NF a ∧ treeWeight a ≤ b := by
  simp only [normalNormBall, Finset.mem_filter, mem_rawNormBall]
  exact and_comm

theorem finite_normalNormBall (b : Nat) :
    Set.Finite {a : ONote | ONote.NF a ∧ treeWeight a ≤ b} := by
  have heq : {a : ONote | ONote.NF a ∧ treeWeight a ≤ b} =
      (normalNormBall b : Set ONote) := by
    ext a
    exact (mem_normalNormBall b a).symm
  rw [heq]
  exact (normalNormBall b).finite_toSet

theorem every_normal_input_enumerated (a : NONote) :
    a.1 ∈ normalNormBall (treeWeight a.1) :=
  (mem_normalNormBall _ _).mpr ⟨a.2, le_rfl⟩

/-- The same finite list with normality carried intrinsically in its elements. -/
def notationNormBall (b : Nat) : Finset NONote :=
  (rawNormBall b).subtype ONote.NF

theorem notationNormBall_exact : Targets.ExactNormalNormEnumerator notationNormBall := by
  intro b a
  exact (Finset.mem_subtype (p := ONote.NF) (s := rawNormBall b) (a := a)).trans
    (mem_rawNormBall b a.1)

theorem finiteNormalNormBalls : Targets.FiniteNormalNormBalls := by
  intro b
  have heq : {a : NONote | treeWeight a.1 ≤ b} = (notationNormBall b : Set NONote) := by
    ext a
    exact (notationNormBall_exact b a).symm
  rw [heq]
  exact (notationNormBall b).finite_toSet

#print axioms mem_rawNormBall
#print axioms finite_normalNormBall

end LogicLineages.OrdinalComparison
