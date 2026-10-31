module
public import LogicLineages.OrdinalComparison.SourceOneUnitLiteralProof
public import LogicLineages.OrdinalComparison.SourceAbsoluteObserverUnusedProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.OneUnit.Proof
open AdmissibleAssignment
open AbsoluteObserver.Proof (unusedVector)

theorem unused_scalar_literal {Γ : List Ty} {σ τ : Ty} (h : OrdinalVector (σ :: Γ) τ.level) :
    unusedVector h 0 = inflated τ (h 0) := rfl

/-- The actual unused-binder vector retains the old coordinate as its right
summand, even when the left summand is a positive-abstraction sum. Whole-free
priority is handled by size_add_ge_right, not by replacing the literal tree. -/
theorem unused_size_ge {Γ σ m} (h : OrdinalVector (σ :: Γ) m)
    (j : Fin (m+1)) :
    ordinalPartialSize (h j) ≤ ordinalPartialSize
      (unusedVector h ⟨j.val, by have := j.isLt; omega⟩) := by
  simp only [unusedVector, dif_pos j.isLt]
  exact size_add_ge_right _ _

theorem unused_positive_size {Γ : List Ty} {σ τ : Ty} (h : OrdinalVector (σ :: Γ) τ.level)
    (j : Fin (τ.level+1)) (_hj : 0 < j.val) :
    ordinalPartialSize (h j) ≤ ordinalPartialSize
      (unusedVector h ⟨j.val, by have := j.isLt; omega⟩) :=
  unused_size_ge h j

theorem sum_ofFn_mono {n k : Nat} (hn : n ≤ k) (f : Fin n → Nat) (g : Fin k → Nat)
    (h : ∀ i, f i ≤ g ⟨i.val, by have := i.isLt; omega⟩) :
    (List.ofFn f).sum ≤ (List.ofFn g).sum := by
  induction n generalizing k with
  | zero => simp
  | succ n ih =>
      cases k with
      | zero => omega
      | succ k =>
          simp only [List.ofFn_succ,List.sum_cons]
          exact Nat.add_le_add (h 0)
            (ih (by omega) (fun i => f i.succ) (fun i => g i.succ) (fun i => h i.succ))

theorem sum_ofFn_strict_head {n k : Nat} (hn : n ≤ k)
    (f : Fin (n+1) → Nat) (g : Fin (k+1) → Nat)
    (h : ∀ i, f i ≤ g ⟨i.val, by have := i.isLt; omega⟩)
    (h0 : f 0 < g 0) : (List.ofFn f).sum < (List.ofFn g).sum := by
  simp only [List.ofFn_succ,List.sum_cons]
  exact Nat.add_lt_add_of_lt_of_le h0
    (sum_ofFn_mono hn (fun i => f i.succ) (fun i => g i.succ) (fun i => h i.succ))

theorem multiplier_positive {Γ σ m} (h : OrdinalVector (σ :: Γ) m) :
    0 < multiplier h := by
  have hs : 0 < ((List.ofFn h).map ordinalPartialSize).sum := by
    rw [List.map_ofFn,List.ofFn_succ]
    simp only [List.sum_cons,Function.comp_apply]
    have := size_pos (h 0)
    omega
  exact Nat.mul_pos (Nat.pow_pos (by decide)) hs

theorem unused_scalar_size_strict {Γ : List Ty} {σ τ : Ty} (h : OrdinalVector (σ :: Γ) τ.level)
    (hf : ordinalHeadFree (h 0)=false) :
    ordinalPartialSize (h 0) < ordinalPartialSize (unusedVector h 0) := by
  rw [unused_scalar_literal,inflated_size τ (h 0) hf]
  have hk : 0 < copies τ := by unfold copies; omega
  unfold coefficient
  rw [Nat.add_mul,Nat.one_mul]
  omega

theorem unused_sum_strict {Γ : List Ty} {σ τ : Ty} (h : OrdinalVector (σ :: Γ) τ.level)
    (hf : ordinalHeadFree (h 0)=false) :
    ((List.ofFn h).map ordinalPartialSize).sum <
      ((List.ofFn (unusedVector h)).map ordinalPartialSize).sum := by
  simp only [List.map_ofFn]
  exact sum_ofFn_strict_head (Nat.le_max_right 1 τ.level)
    (fun j => ordinalPartialSize (h j)) (fun j => ordinalPartialSize (unusedVector h j))
    (unused_size_ge h) (unused_scalar_size_strict h hf)

theorem unused_multiplier_strict {Γ : List Ty} {σ τ : Ty} (h : OrdinalVector (σ :: Γ) τ.level)
    (hf : ordinalHeadFree (h 0)=false) : multiplier h < multiplier (unusedVector h) := by
  exact Nat.mul_lt_mul_of_pos_left (unused_sum_strict h hf) (Nat.pow_pos (by decide))
end LogicLineages.OrdinalComparison.Source.OneUnit.Proof
