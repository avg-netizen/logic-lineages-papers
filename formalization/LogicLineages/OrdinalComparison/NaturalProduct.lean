module
public import LogicLineages.OrdinalComparison.NaturalArithmeticTargets
public import LogicLineages.OrdinalComparison.NaturalSum

@[expose] public section

/-! Literal paired-monomial natural-product algorithm. Exponents are combined
by the existing natural-sum merge; coefficients are multiplied and all output
monomials are collected by the same merge. Normality and the source tree-norm
bound are separate from the still-pending actual-denotation certificate.
-/

namespace LogicLineages.OrdinalComparison

open Vendor.R1

def rawMonomialProduct (e : ONote) (c : ℕ+) : ONote → ONote
  | .zero => .zero
  | .oadd f d u => rawNaturalSum
      (.oadd (rawNaturalSum e f) (c * d) .zero) (rawMonomialProduct e c u)

def rawNaturalProduct : ONote → ONote → ONote
  | .zero, _ => .zero
  | .oadd e c t, b =>
      rawNaturalSum (rawMonomialProduct e c b) (rawNaturalProduct t b)

theorem rawMonomialProduct_normal (e : ONote) (he : ONote.NF e) (c : ℕ+) :
    ∀ b : ONote, ONote.NF b → ONote.NF (rawMonomialProduct e c b)
  | .zero, _ => ONote.NF.zero
  | .oadd f d u, hb =>
      rawNaturalSum_normal _ _
        (ONote.NF.oadd (rawNaturalSum_normal e f he hb.fst) (c * d) ONote.NFBelow.zero)
        (rawMonomialProduct_normal e he c u hb.snd)

theorem rawNaturalProduct_normal : ∀ a : ONote, ONote.NF a →
    ∀ b : ONote, ONote.NF b → ONote.NF (rawNaturalProduct a b)
  | .zero, _, _, _ => ONote.NF.zero
  | .oadd e c t, ha, b, hb =>
      rawNaturalSum_normal _ _ (rawMonomialProduct_normal e ha.fst c b hb)
        (rawNaturalProduct_normal t ha.snd b hb)

theorem one_add_add_le_weight_product (a b : Nat) :
    1 + (a + b) ≤ (1 + a) * (1 + b) := by
  simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
  omega

theorem rawMonomialProduct_norm (e : ONote) (c : ℕ+) (b : ONote) :
    treeWeight (rawMonomialProduct e c b) ≤
      (c : Nat) * (1 + treeWeight e) * treeWeight b := by
  induction b with
  | zero => simp only [rawMonomialProduct, treeWeight, Nat.mul_zero, Nat.le_refl]
  | oadd f d u ihf ihu =>
      simp only [rawMonomialProduct, rawNaturalSum_norm, treeWeight, PNat.mul_coe,
        Nat.add_zero]
      have hnode := Nat.mul_le_mul_left ((c : Nat) * (d : Nat))
        (one_add_add_le_weight_product (treeWeight e) (treeWeight f))
      calc
        (c : Nat) * (d : Nat) * (1 + (treeWeight e + treeWeight f)) +
            treeWeight (rawMonomialProduct e c u) ≤
          (c : Nat) * (d : Nat) * ((1 + treeWeight e) * (1 + treeWeight f)) +
            (c : Nat) * (1 + treeWeight e) * treeWeight u :=
          Nat.add_le_add hnode ihu
        _ = (c : Nat) * (1 + treeWeight e) *
            ((d : Nat) * (1 + treeWeight f) + treeWeight u) := by
          have hfactor : (c : Nat) * (d : Nat) *
              ((1 + treeWeight e) * (1 + treeWeight f)) =
              (c : Nat) * (1 + treeWeight e) * ((d : Nat) * (1 + treeWeight f)) := by
            ac_rfl
          rw [hfactor, ← Nat.mul_add]

theorem rawNaturalProduct_norm (a b : ONote) :
    treeWeight (rawNaturalProduct a b) ≤ treeWeight a * treeWeight b := by
  induction a with
  | zero => simp only [rawNaturalProduct, treeWeight, Nat.zero_mul, Nat.le_refl]
  | oadd e c t ihe iht =>
      simp only [rawNaturalProduct, rawNaturalSum_norm, treeWeight]
      calc
        treeWeight (rawMonomialProduct e c b) + treeWeight (rawNaturalProduct t b) ≤
            ((c : Nat) * (1 + treeWeight e)) * treeWeight b +
              treeWeight t * treeWeight b :=
          Nat.add_le_add (rawMonomialProduct_norm e c b) iht
        _ = ((c : Nat) * (1 + treeWeight e) + treeWeight t) * treeWeight b :=
          (Nat.add_mul _ _ _).symm

def naturalProduct (a b : NONote) : NONote :=
  ⟨rawNaturalProduct a.1 b.1, rawNaturalProduct_normal a.1 a.2 b.1 b.2⟩

theorem naturalProductNormBound : Targets.NaturalProductNormBound naturalProduct :=
  fun a b => rawNaturalProduct_norm a.1 b.1

end LogicLineages.OrdinalComparison
