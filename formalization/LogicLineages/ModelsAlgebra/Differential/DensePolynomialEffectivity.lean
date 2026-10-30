module

public import LogicLineages.ModelsAlgebra.Differential.DensePolynomialTargets
public import LogicLineages.ModelsAlgebra.Differential.RationalCode

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.DensePolynomial

theorem add_primitive_recursive : Primrec₂ add := by
  change Primrec (fun t : Code × Code =>
    (List.range (max t.1.length t.2.length)).map fun i =>
      RationalCode.add (t.1.getD i RationalCode.zero) (t.2.getD i RationalCode.zero))
  exact Primrec.list_map
    (Primrec.list_range.comp (Primrec.nat_max.comp
      (Primrec.list_length.comp Primrec.fst) (Primrec.list_length.comp Primrec.snd)))
    ((RationalCode.add_primitive_recursive.comp
      ((Primrec.list_getD RationalCode.zero).comp (Primrec.fst.comp Primrec.fst) Primrec.snd)
      ((Primrec.list_getD RationalCode.zero).comp (Primrec.snd.comp Primrec.fst) Primrec.snd)).to₂)

theorem neg_primitive_recursive : Primrec neg :=
  Primrec.list_map Primrec.id (RationalCode.neg_primitive_recursive.comp Primrec.snd).to₂

theorem scale_primitive_recursive : Primrec₂ scale :=
  Primrec.list_map Primrec.snd
    (RationalCode.mul_primitive_recursive.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂

theorem mul_primitive_recursive : Primrec₂ mul := by
  have h : Primrec (fun t : Code × Code =>
      t.1.foldr (fun c acc => add (scale c t.2) (RationalCode.zero :: acc)) []) :=
    Primrec.list_foldr Primrec.fst (Primrec.const [])
      ((add_primitive_recursive.comp
        (scale_primitive_recursive.comp (Primrec.fst.comp Primrec.snd)
          (Primrec.snd.comp Primrec.fst))
        (Primrec.list_cons.comp (Primrec.const RationalCode.zero)
          (Primrec.snd.comp Primrec.snd))).to₂)
  apply h.of_eq
  intro t
  induction t.1 with
  | nil => rfl
  | cons c cs ih => simp only [List.foldr_cons, mul, ih]

theorem power_primitive_recursive : Primrec₂ power := by
  have h : Primrec (fun t : Code × ℕ =>
      Nat.rec (motive := fun _ => Code) [RationalCode.one] (fun _ acc => mul t.1 acc) t.2) :=
    Primrec.nat_rec' Primrec.snd (Primrec.const [RationalCode.one])
      ((mul_primitive_recursive.comp (Primrec.fst.comp Primrec.fst)
        (Primrec.snd.comp Primrec.snd)).to₂)
  apply h.of_eq
  intro t
  induction t.2 with
  | zero => rfl
  | succ n ih => simp only [Nat.rec_add_one, power, ih]

theorem derivative_primitive_recursive : Primrec derivative := by
  change Primrec (fun a : Code => (List.range (a.length - 1)).map fun i =>
    RationalCode.mul (((i + 1, 0), 0) : RationalCode.Code)
      (a.getD (i + 1) RationalCode.zero))
  exact Primrec.list_map
    (Primrec.list_range.comp (Primrec.nat_sub.comp Primrec.list_length (Primrec.const 1)))
    ((RationalCode.mul_primitive_recursive.comp
      (((Primrec.nat_add.comp Primrec.snd (Primrec.const 1)).pair
        (Primrec.const 0)).pair (Primrec.const 0))
      ((Primrec.list_getD RationalCode.zero).comp Primrec.fst
        (Primrec.nat_add.comp Primrec.snd (Primrec.const 1)))).to₂)

theorem isZero_primitive_recursive : Primrec isZero := by
  have h : Primrec (fun a : Code => a.foldr
      (fun c acc => RationalCode.isZero c && acc) true) :=
    Primrec.list_foldr Primrec.id (Primrec.const true)
      ((Primrec.and.comp
        (RationalCode.isZero_primitive_recursive.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.snd.comp Primrec.snd)).to₂)
  apply h.of_eq
  intro a
  induction a with
  | nil => rfl
  | cons c cs ih => simp only [List.foldr_cons, isZero, List.all_cons, ih]

theorem arithmetic_primitive_recursive : Targets.densePolynomialArithmeticPrimitiveRecursive :=
  ⟨add_primitive_recursive, neg_primitive_recursive, scale_primitive_recursive,
    mul_primitive_recursive, power_primitive_recursive, derivative_primitive_recursive,
    isZero_primitive_recursive⟩

end LogicLineages.ModelsAlgebra.Differential.DensePolynomial
