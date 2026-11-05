module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NormalFormTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovInverseProof
public import LogicLineages.OrdinalComparison.LayeredComparison.IntegerAlgorithmsProof
public import Mathlib.Computability.Primrec.List
public import Mathlib.Tactic.SplitIfs
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NormalFormCodeProof
open NormalForm
attribute [local irreducible] Nat.sqrt Nat.unpair

private theorem binary_primitive (base label : Nat) :
    Primrec₂ (fun a b : Nat => base * Nat.pair a b + label) :=
  Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const base) Primrec₂.natPair)
    (Primrec.const label)
private theorem unary_primitive (base label : Nat) :
    Primrec (fun a : Nat => base * a + label) :=
  Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const base) Primrec.id)
    (Primrec.const label)
private theorem numeral_primitive : Primrec WindowCode.numeral :=
  Primrec.nat_mul.comp (Primrec.const 10) Primrec.id
private theorem var_primitive : Primrec WindowCode.var := unary_primitive 10 1
private theorem phi_primitive : Primrec WindowCode.phi := unary_primitive 10 6
private theorem hyper_primitive : Primrec HyperWindowCode.hyper := unary_primitive 10 7
private theorem less_primitive : Primrec₂ WindowCode.less := binary_primitive 8 3
private theorem negative_primitive : Primrec WindowCode.negative := unary_primitive 8 5
private theorem conjunction_primitive : Primrec₂ WindowCode.conjunction := binary_primitive 8 6
private theorem add_primitive : Primrec₂ WindowCode.add := binary_primitive 10 2
private theorem subtract_primitive : Primrec₂ WindowCode.subtract := binary_primitive 10 3
private theorem multiply_primitive : Primrec₂ WindowCode.multiply := binary_primitive 10 4

private theorem toNat_primitive : Primrec Int.toNat := by
  apply (Primrec.ite
    (Primrec.eq.comp IntegerAlgorithms.Proof.sign_primitive (Primrec.const (-1 : Int)))
    (Primrec.const 0) IntegerAlgorithms.Proof.abs_primitive).of_eq
  intro z
  cases z with
  | ofNat n => cases n <;> rfl
  | negSucc n => rfl
private theorem int_sub_primitive : Primrec₂ (fun a b : Int => a - b) := by
  apply (IntegerAlgorithms.Proof.add_primitive.comp Primrec.fst
    (IntegerAlgorithms.Proof.negate_primitive.comp Primrec.snd)).of_eq
  intro p
  exact (sub_eq_add_neg _ _).symm
private theorem shift_primitive : Primrec₂ WindowCode.shift :=
  subtract_primitive.comp
    (add_primitive.comp Primrec.fst (numeral_primitive.comp (toNat_primitive.comp Primrec.snd)))
    (numeral_primitive.comp (toNat_primitive.comp
      (IntegerAlgorithms.Proof.negate_primitive.comp Primrec.snd)))
private theorem atMost_primitive : Primrec₂ WindowCode.atMost :=
  negative_primitive.comp (less_primitive.comp Primrec.snd Primrec.fst)

private theorem item_tag_primitive : Primrec (fun s : Code.ItemData => s.1) := Primrec.fst
private theorem item_name_primitive : Primrec (fun s : Code.ItemData => s.2.1) :=
  Primrec.fst.comp Primrec.snd
private theorem item_index_primitive : Primrec (fun s : Code.ItemData => s.2.2.1) :=
  Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
private theorem item_outer_primitive : Primrec (fun s : Code.ItemData => s.2.2.2) :=
  Primrec.snd.comp (Primrec.snd.comp Primrec.snd)

theorem itemTerm_primitive : Primrec Code.itemTerm := by
  have hv := var_primitive.comp item_name_primitive
  have hs := shift_primitive.comp hv item_index_primitive
  have hhyper := phi_primitive.comp
    (shift_primitive.comp (hyper_primitive.comp hs) item_outer_primitive)
  exact Primrec.ite (Primrec.eq.comp item_tag_primitive (Primrec.const 0)) hv
    (Primrec.ite (Primrec.eq.comp item_tag_primitive (Primrec.const 1))
      (phi_primitive.comp hs) hhyper)

private theorem hyperThreshold_primitive : Primrec hyperThreshold := by
  have hr : Primrec hyperRequired :=
    toNat_primitive.comp IntegerAlgorithms.Proof.negate_primitive
  exact Primrec.ite (Primrec.nat_le.comp hr (Primrec.const 1)) (Primrec.const 0)
    (Primrec.succ.comp (SnyatkovInverse.Proof.actualPrimitiveRecursion.2.1.comp
      (Primrec.nat_sub.comp hr (Primrec.const 1))))

theorem itemCutoff_primitive : Primrec Code.itemCutoff :=
  Primrec.ite (Primrec.eq.comp item_tag_primitive (Primrec.const 0)) (Primrec.const 0)
    (Primrec.ite (Primrec.eq.comp item_tag_primitive (Primrec.const 1))
      (toNat_primitive.comp (IntegerAlgorithms.Proof.negate_primitive.comp item_index_primitive))
      (toNat_primitive.comp (int_sub_primitive.comp
        (IntegerAlgorithms.Proof.ofNat_primitive.comp
          (hyperThreshold_primitive.comp item_outer_primitive)) item_index_primitive)))

private theorem scalarPart_primitive : Primrec₂ Code.scalarPart :=
  toNat_primitive.comp
    (Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const true))
      (IntegerAlgorithms.Proof.negate_primitive.comp Primrec.snd) Primrec.snd)

theorem part_primitive : Primrec₂ Code.part := by
  let A := Bool × Code.RowData
  let I := Int × Code.ItemData
  have hs : Primrec (fun p : A × (I × Nat) =>
      WindowCode.add
        (WindowCode.multiply (Code.scalarPart p.1.1 p.2.1.1) (Code.itemTerm p.2.1.2)) p.2.2) :=
    add_primitive.comp
      (multiply_primitive.comp
        (scalarPart_primitive.comp (Primrec.fst.comp Primrec.fst)
          (Primrec.fst.comp (Primrec.fst.comp Primrec.snd)))
        (itemTerm_primitive.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))))
      (Primrec.snd.comp Primrec.snd)
  have hf : Primrec (fun p : A => p.2.2.foldr
      (fun a rest => WindowCode.add
        (WindowCode.multiply (Code.scalarPart p.1 a.1) (Code.itemTerm a.2)) rest)
      (WindowCode.numeral 0)) :=
    Primrec.list_foldr (Primrec.snd.comp Primrec.snd) (Primrec.const (WindowCode.numeral 0)) hs.to₂
  exact add_primitive.comp
    (numeral_primitive.comp (scalarPart_primitive.comp Primrec.fst
      (Primrec.fst.comp Primrec.snd))) hf

private theorem part_false_primitive : Primrec (Code.part false) :=
  part_primitive.comp (Primrec.const false) Primrec.id
private theorem part_true_primitive : Primrec (Code.part true) :=
  part_primitive.comp (Primrec.const true) Primrec.id
private theorem absolute_primitive : Primrec Code.absolute :=
  add_primitive.comp
    (subtract_primitive.comp part_false_primitive part_true_primitive)
    (subtract_primitive.comp part_true_primitive part_false_primitive)
private theorem nonnegative_primitive : Primrec Code.nonnegative :=
  atMost_primitive.comp part_true_primitive part_false_primitive
private theorem divisible_primitive : Primrec₂ Code.divisible :=
  (binary_primitive 8 4).comp (Primrec.succ.comp Primrec.fst)
    (absolute_primitive.comp Primrec.snd)

theorem atom_primitive : Primrec Code.atom :=
  Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 0))
    (nonnegative_primitive.comp (Primrec.snd.comp Primrec.snd))
    (divisible_primitive.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd))

private theorem domainRowData_primitive : Primrec Code.domainRowData := by
  have hitem : Primrec (fun s : Code.ItemData =>
      ((0 : Nat), s.2.1, (0 : Int), (0 : Int))) :=
    (Primrec.const 0).pair (item_name_primitive.pair
      ((Primrec.const (0 : Int)).pair (Primrec.const (0 : Int))))
  have hlist : Primrec (fun s : Code.ItemData =>
      [((1 : Int), ((0 : Nat), s.2.1, (0 : Int), (0 : Int)))]) :=
    Primrec.list_cons.comp ((Primrec.const (1 : Int)).pair hitem) (Primrec.const [])
  exact (IntegerAlgorithms.Proof.negate_primitive.comp
    (IntegerAlgorithms.Proof.ofNat_primitive.comp itemCutoff_primitive)).pair hlist

theorem domains_primitive : Primrec Code.domains := by
  have hs : Primrec (fun p : Code.RowData × ((Int × Code.ItemData) × Nat) =>
      WindowCode.conjunction (Code.nonnegative (Code.domainRowData p.2.1.2)) p.2.2) :=
    conjunction_primitive.comp
      (nonnegative_primitive.comp (domainRowData_primitive.comp
        (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))))
      (Primrec.snd.comp Primrec.snd)
  exact Primrec.list_foldr Primrec.snd (Primrec.const 0) hs.to₂

private def formulaChildren (code : Nat) : List Nat :=
  if code % 6 = 0 ∨ code % 6 = 1 ∨ code % 6 = 2 then []
  else if code % 6 = 3 then [code / 6]
  else [(code / 6).unpair.1, (code / 6).unpair.2]

private def formulaAssemble (code : Nat) (values : List Nat) : Nat :=
  if code % 6 = 0 then 0
  else if code % 6 = 1 then 1
  else if code % 6 = 2 then Code.atom
    ((Encodable.decode (code / 6) : Option Code.AtomData).getD (0, 0, (0 : Int), []))
  else if code % 6 = 3 then WindowCode.negative (values.getD 0 0)
  else 8 * Nat.pair (values.getD 0 0) (values.getD 1 0) + (code % 6 + 2)

private theorem formula_decreasing : ∀ code child, child ∈ formulaChildren code → child < code := by
  intro code child h
  by_cases hleaf : code % 6 = 0 ∨ code % 6 = 1 ∨ code % 6 = 2
  · simp [formulaChildren, hleaf] at h
  have hpos : 0 < code := by omega
  have hd : code / 6 < code := Nat.div_lt_self hpos (by decide)
  have hl := Nat.unpair_left_le (code / 6)
  have hr := Nat.unpair_right_le (code / 6)
  unfold formulaChildren at h
  split_ifs at h <;> simp_all only [List.mem_cons, List.not_mem_nil, or_false]
  all_goals omega

private theorem formula_equation (code : Nat) :
    Code.formula code = formulaAssemble code ((formulaChildren code).map Code.formula) := by
  rw [Code.formula]
  split_ifs <;> simp_all [formulaChildren, formulaAssemble]

private theorem tag_primitive : Primrec (fun code : Nat => code % 6) :=
  Primrec.nat_mod.comp Primrec.id (Primrec.const 6)
private theorem quotient_primitive : Primrec (fun code : Nat => code / 6) :=
  Primrec.nat_div.comp Primrec.id (Primrec.const 6)
private theorem tag_is (n : Nat) : PrimrecPred (fun code : Nat => code % 6 = n) :=
  Primrec.eq.comp tag_primitive (Primrec.const n)
private theorem left_primitive : Primrec (fun code : Nat => (code / 6).unpair.1) :=
  Primrec.fst.comp (Primrec.unpair.comp quotient_primitive)
private theorem right_primitive : Primrec (fun code : Nat => (code / 6).unpair.2) :=
  Primrec.snd.comp (Primrec.unpair.comp quotient_primitive)
private theorem formulaChildren_primitive : Primrec formulaChildren :=
  Primrec.ite ((tag_is 0).or ((tag_is 1).or (tag_is 2))) (Primrec.const [])
    (Primrec.ite (tag_is 3)
      (Primrec.list_cons.comp quotient_primitive (Primrec.const []))
      (Primrec.list_cons.comp left_primitive
        (Primrec.list_cons.comp right_primitive (Primrec.const []))))

private theorem formulaAssemble_primitive : Primrec₂ formulaAssemble := by
  let A := Nat × List Nat
  have hd : Primrec (fun p : A =>
      (Encodable.decode (p.1 / 6) : Option Code.AtomData).getD (0, 0, (0 : Int), [])) :=
    Primrec.option_getD.comp
      ((Primrec.decode : Primrec (fun n : Nat => (Encodable.decode n : Option Code.AtomData))).comp
        (quotient_primitive.comp Primrec.fst))
      (Primrec.const (0, 0, (0 : Int), []))
  have h0 : Primrec (fun p : A => p.2.getD 0 0) :=
    (Primrec.list_getD (0 : Nat)).comp Primrec.snd (Primrec.const 0)
  have h1 : Primrec (fun p : A => p.2.getD 1 0) :=
    (Primrec.list_getD (0 : Nat)).comp Primrec.snd (Primrec.const 1)
  have hb : Primrec (fun p : A =>
      8 * Nat.pair (p.2.getD 0 0) (p.2.getD 1 0) + (p.1 % 6 + 2)) :=
    Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 8) (Primrec₂.natPair.comp h0 h1))
      (Primrec.nat_add.comp (tag_primitive.comp Primrec.fst) (Primrec.const 2))
  exact Primrec.ite ((tag_is 0).comp Primrec.fst) (Primrec.const 0)
    (Primrec.ite ((tag_is 1).comp Primrec.fst) (Primrec.const 1)
      (Primrec.ite ((tag_is 2).comp Primrec.fst) (atom_primitive.comp hd)
        (Primrec.ite ((tag_is 3).comp Primrec.fst) (negative_primitive.comp h0) hb)))

/-- The upstream primitive course-of-values recursion theorem applies directly
because the frozen compiler only reads strictly smaller numeric codes. -/
private def formulaStep (values : List Nat) : Option Nat :=
  some (formulaAssemble values.length
    ((formulaChildren values.length).map (fun i => values.getD i 0)))

private theorem formulaStep_primitive : Primrec formulaStep := by
  have hs : Primrec (fun p : List Nat × Nat => p.1.getD p.2 0) :=
    (Primrec.list_getD (0 : Nat)).comp Primrec.fst Primrec.snd
  have hm : Primrec (fun values : List Nat =>
      (formulaChildren values.length).map (fun i => values.getD i 0)) :=
    Primrec.list_map (formulaChildren_primitive.comp Primrec.list_length) hs.to₂
  exact Primrec.option_some.comp (formulaAssemble_primitive.comp Primrec.list_length hm)

theorem formula_primitive : Primrec Code.formula := by
  have h : Primrec₂ (fun (_ : Unit) (code : Nat) => Code.formula code) := by
    apply Primrec.nat_strong_rec _ (formulaStep_primitive.comp Primrec.snd).to₂
    intro _ code
    unfold formulaStep
    simp only [List.length_map, List.length_range]
    apply congrArg some
    rw [formula_equation code]
    apply congrArg (formulaAssemble code)
    apply List.map_congr_left
    intro i hi
    have hlt := formula_decreasing code i hi
    simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hlt]
  exact h.comp (Primrec.const ()) Primrec.id

theorem formula_computable : Computable Code.formula := formula_primitive.to_comp

theorem actualNumericPrograms : NormalFormTargets.ActualNumericPrograms :=
  ⟨itemTerm_primitive, itemCutoff_primitive, part_primitive, domains_primitive,
    atom_primitive, formula_computable⟩

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NormalFormCodeProof
