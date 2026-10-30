module

public import LogicLineages.ModelsAlgebra.Differential.RationalCodeTargets
public import Mathlib.Data.Rat.Cast.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Differential.RationalCode

private theorem denominator_ne_zero (a : Code) : (a.2 : ℚ) + 1 ≠ 0 := by
  positivity

private theorem product_denominator (a b : Code) :
    (((a.2 + 1) * (b.2 + 1) - 1 : ℕ) : ℚ) + 1 =
      ((a.2 : ℚ) + 1) * ((b.2 : ℚ) + 1) := by
  have hp : 1 ≤ (a.2 + 1) * (b.2 + 1) := Nat.mul_pos (by omega) (by omega)
  have h := congrArg (fun n : ℕ => (n : ℚ)) (Nat.sub_add_cancel hp)
  simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_mul] using h

theorem value_zero : value zero = 0 := by simp [zero, value]
theorem value_one : value one = 1 := by simp [one, value]

theorem value_add (a b : Code) : value (add a b) = value a + value b := by
  dsimp [value, add]
  rw [product_denominator]
  push_cast
  field_simp [denominator_ne_zero a, denominator_ne_zero b]
  <;> ring

theorem value_neg (a : Code) : value (neg a) = -value a := by
  dsimp [value, neg]
  ring

theorem value_mul (a b : Code) : value (mul a b) = value a * value b := by
  dsimp [value, mul]
  rw [product_denominator]
  push_cast
  field_simp [denominator_ne_zero a, denominator_ne_zero b]
  <;> ring

theorem value_inverse (a : Code) : value (inverse a) = (value a)⁻¹ := by
  by_cases he : a.1.1 = a.1.2
  · simp [inverse, he, value, zero]
  · by_cases hle : a.1.2 ≤ a.1.1
    · have hpos : 1 ≤ a.1.1 - a.1.2 := by omega
      have h := congrArg (fun n : ℕ => (n : ℚ)) (Nat.sub_add_cancel hpos)
      have hd : ((a.1.1 - a.1.2 - 1 : ℕ) : ℚ) + 1 =
          (a.1.1 : ℚ) - (a.1.2 : ℚ) := by
        simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_sub hle] using h
      simp only [inverse, if_neg he, if_pos hle, value, Prod.fst, Prod.snd,
        Nat.cast_add, Nat.cast_one, Nat.cast_zero, sub_zero]
      rw [hd, inv_div]
    · have hlt : a.1.1 < a.1.2 := Nat.lt_of_not_ge hle
      have hpos : 1 ≤ a.1.2 - a.1.1 := by omega
      have h := congrArg (fun n : ℕ => (n : ℚ)) (Nat.sub_add_cancel hpos)
      have hd : ((a.1.2 - a.1.1 - 1 : ℕ) : ℚ) + 1 =
          (a.1.2 : ℚ) - (a.1.1 : ℚ) := by
        simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_sub hlt.le] using h
      simp only [inverse, if_neg he, if_neg hle, value, Prod.fst, Prod.snd,
        Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_sub]
      rw [hd, inv_div]
      have hs : (a.1.1 : ℚ) - (a.1.2 : ℚ) = -((a.1.2 : ℚ) - (a.1.1 : ℚ)) := by ring
      rw [hs]
      simp only [neg_div, div_neg]

theorem value_div (a b : Code) : value (div a b) = value a / value b := by
  rw [div, value_mul, value_inverse, div_eq_mul_inv]

theorem isZero_correct (a : Code) : isZero a = true ↔ value a = 0 := by
  simp [isZero, value, denominator_ne_zero a, sub_eq_zero]

theorem equal_correct (a b : Code) : equal a b = true ↔ value a = value b := by
  rw [equal, isZero_correct, value_add, value_neg, ← sub_eq_add_neg, sub_eq_zero]

theorem coverage : Targets.rationalCodeCoverage := by
  intro q
  have hd : q.den - 1 + 1 = q.den := Nat.sub_add_cancel q.den_pos
  have hcast : ((q.den - 1 : ℕ) : ℚ) + 1 = (q.den : ℚ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using congrArg (fun n : ℕ => (n : ℚ)) hd
  cases hn : q.num with
  | ofNat n =>
    refine ⟨((n, 0), q.den - 1), ?_⟩
    dsimp [value]
    rw [hcast]
    simpa only [hn, Int.ofNat_eq_natCast, Int.cast_natCast, Nat.cast_zero, sub_zero]
      using q.num_div_den
  | negSucc n =>
    refine ⟨((0, n + 1), q.den - 1), ?_⟩
    dsimp [value]
    rw [hcast]
    simpa only [hn, Int.cast_negSucc, Nat.cast_zero, zero_sub, Nat.cast_add, Nat.cast_one]
      using q.num_div_den

theorem arithmetic_correct : Targets.rationalCodeCorrect :=
  ⟨value_zero, value_one, value_add, value_neg, value_mul, value_inverse,
    value_div, isZero_correct, equal_correct⟩

private theorem pr_pos : Primrec (fun a : Code => a.1.1) := Primrec.fst.comp Primrec.fst
private theorem pr_neg : Primrec (fun a : Code => a.1.2) := Primrec.snd.comp Primrec.fst
private theorem pr_den : Primrec (fun a : Code => a.2 + 1) :=
  Primrec.nat_add.comp Primrec.snd (Primrec.const 1)

private theorem pr_triple {α : Type} [Primcodable α] {f g h : α → ℕ}
    (hf : Primrec f) (hg : Primrec g) (hh : Primrec h) :
    Primrec (fun x => ((f x, g x), h x)) := (hf.pair hg).pair hh

private theorem add_primrec_map {α : Type} [Primcodable α] {f g : α → Code}
    (hf : Primrec f) (hg : Primrec g) : Primrec (fun x => add (f x) (g x)) := by
  exact pr_triple
    (Primrec.nat_add.comp
      (Primrec.nat_mul.comp (pr_pos.comp hf) (pr_den.comp hg))
      (Primrec.nat_mul.comp (pr_pos.comp hg) (pr_den.comp hf)))
    (Primrec.nat_add.comp
      (Primrec.nat_mul.comp (pr_neg.comp hf) (pr_den.comp hg))
      (Primrec.nat_mul.comp (pr_neg.comp hg) (pr_den.comp hf)))
    (Primrec.nat_sub.comp
      (Primrec.nat_mul.comp (pr_den.comp hf) (pr_den.comp hg)) (Primrec.const 1))

private theorem mul_primrec_map {α : Type} [Primcodable α] {f g : α → Code}
    (hf : Primrec f) (hg : Primrec g) : Primrec (fun x => mul (f x) (g x)) := by
  exact pr_triple
    (Primrec.nat_add.comp
      (Primrec.nat_mul.comp (pr_pos.comp hf) (pr_pos.comp hg))
      (Primrec.nat_mul.comp (pr_neg.comp hf) (pr_neg.comp hg)))
    (Primrec.nat_add.comp
      (Primrec.nat_mul.comp (pr_pos.comp hf) (pr_neg.comp hg))
      (Primrec.nat_mul.comp (pr_neg.comp hf) (pr_pos.comp hg)))
    (Primrec.nat_sub.comp
      (Primrec.nat_mul.comp (pr_den.comp hf) (pr_den.comp hg)) (Primrec.const 1))

theorem add_primitive_recursive : Primrec₂ add := add_primrec_map Primrec.fst Primrec.snd
theorem mul_primitive_recursive : Primrec₂ mul := mul_primrec_map Primrec.fst Primrec.snd
theorem neg_primitive_recursive : Primrec neg := pr_triple pr_neg pr_pos Primrec.snd

theorem inverse_primitive_recursive : Primrec inverse := by
  exact Primrec.ite (Primrec.eq.comp pr_pos pr_neg) (Primrec.const zero)
    (Primrec.ite (Primrec.nat_le.comp pr_neg pr_pos)
      (pr_triple pr_den (Primrec.const 0)
        (Primrec.nat_sub.comp (Primrec.nat_sub.comp pr_pos pr_neg) (Primrec.const 1)))
      (pr_triple (Primrec.const 0) pr_den
        (Primrec.nat_sub.comp (Primrec.nat_sub.comp pr_neg pr_pos) (Primrec.const 1))))

theorem div_primitive_recursive : Primrec₂ div :=
  mul_primrec_map Primrec.fst (inverse_primitive_recursive.comp Primrec.snd)

theorem isZero_primitive_recursive : Primrec isZero :=
  (Primrec.eq.comp pr_pos pr_neg).decide

theorem equal_primitive_recursive : Primrec₂ equal :=
  isZero_primitive_recursive.comp
    (add_primrec_map Primrec.fst (neg_primitive_recursive.comp Primrec.snd))

theorem arithmetic_primitive_recursive : Targets.rationalCodePrimitiveRecursive :=
  ⟨add_primitive_recursive, neg_primitive_recursive, mul_primitive_recursive,
    inverse_primitive_recursive, div_primitive_recursive, isZero_primitive_recursive,
    equal_primitive_recursive⟩

theorem codec_roundtrip : Targets.rationalCodeRoundtrip := Encodable.encodek

end LogicLineages.ModelsAlgebra.Differential.RationalCode
