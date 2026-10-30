module

public import LogicLineages.ModelsAlgebra.Differential.NumericDeterminantTargets
public import LogicLineages.ModelsAlgebra.Differential.DensePolynomialEffectivity

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.NumericDeterminant

private theorem nat_power_primitive_recursive : Primrec₂ ((· ^ ·) : ℕ → ℕ → ℕ) :=
  Primrec₂.unpaired'.1 Nat.Primrec.pow

theorem digit_primitive_recursive :
    Primrec (fun t : ℕ × ℕ × ℕ => digit t.1 t.2.1 t.2.2) := by
  have hn : Primrec (fun t : ℕ × ℕ × ℕ => t.1) := Primrec.fst
  have hk : Primrec (fun t : ℕ × ℕ × ℕ => t.2.1) := Primrec.fst.comp Primrec.snd
  have hi : Primrec (fun t : ℕ × ℕ × ℕ => t.2.2) := Primrec.snd.comp Primrec.snd
  have hb := Primrec.nat_add.comp hn (Primrec.const 2)
  have hp := nat_power_primitive_recursive.comp hb hi
  have hd := Primrec.nat_div.comp hk hp
  exact (Primrec.nat_mod.comp hd hb).of_eq (fun _ => rfl)

private theorem all_eq_foldr {α : Type*} (f : α → Bool) (l : List α) :
    l.all f = l.foldr (fun i acc => f i && acc) true := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.all_cons, List.foldr_cons, ih]

theorem valid_primitive_recursive : Primrec₂ valid := by
  have hn : Primrec (fun t : (ℕ × ℕ) × (ℕ × Bool) => t.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hk : Primrec (fun t : (ℕ × ℕ) × (ℕ × Bool) => t.1.2) :=
    Primrec.snd.comp Primrec.fst
  have hi : Primrec (fun t : (ℕ × ℕ) × (ℕ × Bool) => t.2.1) :=
    Primrec.fst.comp Primrec.snd
  have ha : Primrec (fun t : (ℕ × ℕ) × (ℕ × Bool) => t.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hd := digit_primitive_recursive.comp (hn.pair (hk.pair hi))
  have ht := (Primrec.nat_lt.comp hd hn).decide
  have hs := Primrec.and.comp ht ha
  have h := Primrec.list_foldr (Primrec.list_range.comp
    (show Primrec (fun t : ℕ × ℕ => t.1) from Primrec.fst)) (Primrec.const true) hs.to₂
  exact h.of_eq (fun t => (all_eq_foldr (fun i => decide (digit t.1 t.2 i < t.1))
    (List.range t.1)).symm)

theorem pairSign_primitive_recursive : Primrec₂ pairSign := by
  have hlt : PrimrecPred (fun t : ℕ × ℕ => t.1 < t.2) := Primrec.nat_lt
  have hgt : PrimrecPred (fun t : ℕ × ℕ => t.2 < t.1) :=
    Primrec.nat_lt.comp Primrec.snd Primrec.fst
  have hn := Primrec.ite hgt (Primrec.const (RationalCode.neg RationalCode.one))
    (Primrec.const RationalCode.zero)
  exact (Primrec.ite hlt (Primrec.const RationalCode.one) hn).of_eq (fun _ => rfl)

private def rowWeight (n k j : ℕ) : RationalCode.Code :=
  (List.range j).foldr (fun i acc =>
    RationalCode.mul (pairSign (digit n k i) (digit n k j)) acc) RationalCode.one

private theorem rowWeight_step_primitive_recursive :
    Primrec (fun t : (ℕ × ℕ × ℕ) × (ℕ × RationalCode.Code) =>
      RationalCode.mul (pairSign (digit t.1.1 t.1.2.1 t.2.1)
        (digit t.1.1 t.1.2.1 t.1.2.2)) t.2.2) := by
  have hn : Primrec (fun t : (ℕ × ℕ × ℕ) × (ℕ × RationalCode.Code) => t.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hk : Primrec (fun t : (ℕ × ℕ × ℕ) × (ℕ × RationalCode.Code) => t.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hj : Primrec (fun t : (ℕ × ℕ × ℕ) × (ℕ × RationalCode.Code) => t.1.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have hi : Primrec (fun t : (ℕ × ℕ × ℕ) × (ℕ × RationalCode.Code) => t.2.1) :=
    Primrec.fst.comp Primrec.snd
  have ha : Primrec (fun t : (ℕ × ℕ × ℕ) × (ℕ × RationalCode.Code) => t.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hdi := digit_primitive_recursive.comp (hn.pair (hk.pair hi))
  have hdj := digit_primitive_recursive.comp (hn.pair (hk.pair hj))
  have hp := pairSign_primitive_recursive.comp hdi hdj
  exact RationalCode.mul_primitive_recursive.comp hp ha

private theorem rowWeight_primitive_recursive :
    Primrec (fun t : ℕ × ℕ × ℕ => rowWeight t.1 t.2.1 t.2.2) := by
  have hj : Primrec (fun t : ℕ × ℕ × ℕ => t.2.2) := Primrec.snd.comp Primrec.snd
  have h := Primrec.list_foldr (Primrec.list_range.comp hj) (Primrec.const RationalCode.one)
    rowWeight_step_primitive_recursive.to₂
  exact h.of_eq (fun _ => rfl)

theorem weight_primitive_recursive : Primrec₂ weight := by
  have hn : Primrec (fun t : (ℕ × ℕ) × (ℕ × RationalCode.Code) => t.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hk : Primrec (fun t : (ℕ × ℕ) × (ℕ × RationalCode.Code) => t.1.2) :=
    Primrec.snd.comp Primrec.fst
  have hj : Primrec (fun t : (ℕ × ℕ) × (ℕ × RationalCode.Code) => t.2.1) :=
    Primrec.fst.comp Primrec.snd
  have ha : Primrec (fun t : (ℕ × ℕ) × (ℕ × RationalCode.Code) => t.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hr := rowWeight_primitive_recursive.comp (hn.pair (hk.pair hj))
  have hs := RationalCode.mul_primitive_recursive.comp hr ha
  have h := Primrec.list_foldr (Primrec.list_range.comp
    (show Primrec (fun t : ℕ × ℕ => t.1) from Primrec.fst))
    (Primrec.const RationalCode.one) hs.to₂
  exact h.of_eq (fun _ => rfl)

theorem entry_primitive_recursive :
    Primrec (fun t : ℕ × MatrixCode × ℕ × ℕ => entry t.1 t.2.1 t.2.2.1 t.2.2.2) := by
  have hn : Primrec (fun t : ℕ × MatrixCode × ℕ × ℕ => t.1) := Primrec.fst
  have hm : Primrec (fun t : ℕ × MatrixCode × ℕ × ℕ => t.2.1) := Primrec.fst.comp Primrec.snd
  have hi : Primrec (fun t : ℕ × MatrixCode × ℕ × ℕ => t.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hj : Primrec (fun t : ℕ × MatrixCode × ℕ × ℕ => t.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hidx := Primrec.nat_add.comp (Primrec.nat_mul.comp hi hn) hj
  exact (Primrec.list_getD ([] : DensePolynomial.Code)).comp hm hidx

private theorem product_step_primitive_recursive :
    Primrec (fun t : (ℕ × MatrixCode × ℕ) × (ℕ × DensePolynomial.Code) =>
      DensePolynomial.mul (entry t.1.1 t.1.2.1 (digit t.1.1 t.1.2.2 t.2.1) t.2.1) t.2.2) := by
  have hn : Primrec (fun t : (ℕ × MatrixCode × ℕ) × (ℕ × DensePolynomial.Code) => t.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hm : Primrec (fun t : (ℕ × MatrixCode × ℕ) × (ℕ × DensePolynomial.Code) => t.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hk : Primrec (fun t : (ℕ × MatrixCode × ℕ) × (ℕ × DensePolynomial.Code) => t.1.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have hi : Primrec (fun t : (ℕ × MatrixCode × ℕ) × (ℕ × DensePolynomial.Code) => t.2.1) :=
    Primrec.fst.comp Primrec.snd
  have ha : Primrec (fun t : (ℕ × MatrixCode × ℕ) × (ℕ × DensePolynomial.Code) => t.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hd := digit_primitive_recursive.comp (hn.pair (hk.pair hi))
  have he := entry_primitive_recursive.comp (hn.pair (hm.pair (hd.pair hi)))
  exact DensePolynomial.mul_primitive_recursive.comp he ha

theorem product_primitive_recursive :
    Primrec (fun t : ℕ × MatrixCode × ℕ => product t.1 t.2.1 t.2.2) := by
  exact Primrec.list_foldr (Primrec.list_range.comp
    (show Primrec (fun t : ℕ × MatrixCode × ℕ => t.1) from Primrec.fst))
    (Primrec.const [RationalCode.one]) product_step_primitive_recursive.to₂

theorem summand_primitive_recursive :
    Primrec (fun t : ℕ × MatrixCode × ℕ => summand t.1 t.2.1 t.2.2) := by
  have hn : Primrec (fun t : ℕ × MatrixCode × ℕ => t.1) := Primrec.fst
  have hk : Primrec (fun t : ℕ × MatrixCode × ℕ => t.2.2) := Primrec.snd.comp Primrec.snd
  have hv := valid_primitive_recursive.comp hn hk
  have hw := weight_primitive_recursive.comp hn hk
  have hscale := DensePolynomial.scale_primitive_recursive.comp hw product_primitive_recursive
  exact (Primrec.ite (Primrec.eq.comp hv (Primrec.const true)) hscale (Primrec.const [])).of_eq
    (fun _ => rfl)

private theorem determinant_step_primitive_recursive :
    Primrec (fun t : (ℕ × MatrixCode) × (ℕ × DensePolynomial.Code) =>
      DensePolynomial.add (summand t.1.1 t.1.2 t.2.1) t.2.2) := by
  have hn : Primrec (fun t : (ℕ × MatrixCode) × (ℕ × DensePolynomial.Code) => t.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hm : Primrec (fun t : (ℕ × MatrixCode) × (ℕ × DensePolynomial.Code) => t.1.2) :=
    Primrec.snd.comp Primrec.fst
  have hk : Primrec (fun t : (ℕ × MatrixCode) × (ℕ × DensePolynomial.Code) => t.2.1) :=
    Primrec.fst.comp Primrec.snd
  have ha : Primrec (fun t : (ℕ × MatrixCode) × (ℕ × DensePolynomial.Code) => t.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hs := summand_primitive_recursive.comp (hn.pair (hm.pair hk))
  exact DensePolynomial.add_primitive_recursive.comp hs ha

theorem determinant_primitive_recursive : Targets.numericDeterminantPrimitiveRecursive := by
  have hn : Primrec (fun t : ℕ × MatrixCode => t.1) := Primrec.fst
  have hb := Primrec.nat_add.comp hn (Primrec.const 2)
  have hp := nat_power_primitive_recursive.comp hb hn
  exact Primrec.list_foldr (Primrec.list_range.comp hp) (Primrec.const [])
    determinant_step_primitive_recursive.to₂

end LogicLineages.ModelsAlgebra.Differential.NumericDeterminant
