module
public import LogicLineages.PermittedControl.ThickResonanceProof

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

 theorem long_residue_at (f : Nat → Nat) (B : Nat) (hf : SelectedWithThreshold f B)
    (M : Nat) (lam target : Ordinal.{0}) (t i : Nat) (hM : 0 < M)
    (ha : lam < epsilonZero) (hl : Order.IsSuccLimit lam) (htl : Order.IsSuccLimit target)
    (hgap : target+Ordinal.omega0^(2 : Ordinal) ≤ lam)
    (ht : max (actualOrdinalNorm lam) (max (actualOrdinalNorm target+3) (max M B)) ≤ t)
    (hi : FirstEntry f (countInitial lam t) target i) :
    Int.ModEq (M : Int) (i : Int) ((potential t : Int)-(((actualOrdinalNorm target+1)/2 : Nat) : Int)) ∧
    Int.ModEq (2*(M : Int)) (entryNormAt f (countInitial lam t) i : Int)
      (2*(((actualOrdinalNorm target+1)/2 : Nat) : Int)) := by
  have hlt : target < lam :=
    (by simpa using (add_lt_add_iff_left target).mpr (Ordinal.opow_pos (2 : Ordinal) Ordinal.omega0_pos)).trans_le hgap
  obtain ⟨j,hj,horbit,hfinite,hlong⟩ := entryResidues f B hf M lam target t hM ha hl (Or.inr htl) hlt ht
  have heq := firstEntry_unique f _ target j i hj hi
  subst j
  apply hlong
  rintro ⟨k,hk,heq⟩
  have hsmall : target+Ordinal.omega0*(k : Ordinal) < target+Ordinal.omega0^(2 : Ordinal) :=
    (add_lt_add_iff_left target).mpr (by simpa using linear_below_square k 0)
  rw [← heq] at hsmall
  exact (not_lt_of_ge hgap) hsmall

end LogicLineages.PermittedControl
