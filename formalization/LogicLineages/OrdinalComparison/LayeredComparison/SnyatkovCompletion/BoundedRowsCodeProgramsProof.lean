module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BoundedRowsTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NormalFormCodeProgramsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BoundedRowsCodeProof
open BoundedRows
attribute [local irreducible] Nat.sqrt Nat.unpair

private theorem binary_primitive (tag : Nat) :
    Primrec₂ (fun a b : Nat => 6 * Nat.pair a b + tag) :=
  Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 6) Primrec₂.natPair)
    (Primrec.const tag)
private theorem unary_primitive (tag : Nat) :
    Primrec (fun a : Nat => 6 * a + tag) :=
  Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 6) Primrec.id)
    (Primrec.const tag)
private theorem toNat_primitive : Primrec Int.toNat := by
  apply (Primrec.ite
    (Primrec.eq.comp IntegerAlgorithms.Proof.sign_primitive (Primrec.const (-1 : Int)))
    (Primrec.const 0) IntegerAlgorithms.Proof.abs_primitive).of_eq
  intro z
  cases z with
  | ofNat n => cases n <;> rfl
  | negSucc n => rfl
private theorem shift_primitive : Primrec₂ Code.shift :=
  Primrec.nat_sub.comp
    (Primrec.nat_add.comp Primrec.fst (toNat_primitive.comp Primrec.snd))
    (toNat_primitive.comp (IntegerAlgorithms.Proof.negate_primitive.comp Primrec.snd))
private theorem item_tag_primitive : Primrec (fun s : Code.ItemData => s.1) := Primrec.fst
private theorem item_name_primitive : Primrec (fun s : Code.ItemData => s.2.1) :=
  Primrec.fst.comp Primrec.snd
private theorem item_index_primitive : Primrec (fun s : Code.ItemData => s.2.2.1) :=
  Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
private theorem item_outer_primitive : Primrec (fun s : Code.ItemData => s.2.2.2) :=
  Primrec.snd.comp (Primrec.snd.comp Primrec.snd)

theorem itemValue_primitive : Primrec₂ Code.itemValue := by
  have hs : Primrec (fun p : Code.ItemData × Nat => Code.shift p.2 p.1.2.2.1) :=
    shift_primitive.comp Primrec.snd (item_index_primitive.comp Primrec.fst)
  have hh : Primrec (fun p : Code.ItemData × Nat =>
      Phi (Code.shift (FixedSeedControlResidue.H (Code.shift p.2 p.1.2.2.1)) p.1.2.2.2)) :=
    Phi_primrec.comp (shift_primitive.comp
      (FixedSeedControlResidue.Proof.H_primitive.comp hs)
      (item_outer_primitive.comp Primrec.fst))
  exact Primrec.ite
    (Primrec.eq.comp (item_tag_primitive.comp Primrec.fst) (Primrec.const 0)) Primrec.snd
    (Primrec.ite
      (Primrec.eq.comp (item_tag_primitive.comp Primrec.fst) (Primrec.const 1))
      (Phi_primrec.comp hs) hh)

attribute [local irreducible] Code.itemValue

theorem splitItems_primitive :
    Primrec₂ (fun args : Nat × Nat => Code.splitItems args.1 args.2) := by
  let I := Int × Code.ItemData
  let S := Int × List I
  let A := (Nat × Nat) × List I
  have hi : Primrec (fun p : A × (I × S) => p.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hn : Primrec (fun p : A × (I × S) => p.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have ha : Primrec (fun p : A × (I × S) => p.2.1) :=
    Primrec.fst.comp Primrec.snd
  have hrest : Primrec (fun p : A × (I × S) => p.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hvalue : Primrec (fun p : A × (I × S) =>
      p.2.1.1 * (Code.itemValue p.2.1.2 p.1.1.2 : Int) + p.2.2.1) :=
    IntegerAlgorithms.Proof.add_primitive.comp
      (IntegerAlgorithms.Proof.mul_primitive.comp (Primrec.fst.comp ha)
        (IntegerAlgorithms.Proof.ofNat_primitive.comp
          (itemValue_primitive.comp (Primrec.snd.comp ha) hn)))
      (Primrec.fst.comp hrest)
  have hs : Primrec (fun p : A × (I × S) =>
      if p.2.1.2.2.1 = p.1.1.1
      then (p.2.1.1 * (Code.itemValue p.2.1.2 p.1.1.2 : Int) + p.2.2.1, p.2.2.2)
      else (p.2.2.1, p.2.1 :: p.2.2.2)) :=
    Primrec.ite
      (Primrec.eq.comp (item_name_primitive.comp (Primrec.snd.comp ha)) hi)
      (hvalue.pair (Primrec.snd.comp hrest))
      ((Primrec.fst.comp hrest).pair
        (Primrec.list_cons.comp ha (Primrec.snd.comp hrest)))
  exact Primrec.list_foldr Primrec.snd (Primrec.const ((0 : Int), ([] : List I))) hs.to₂

attribute [local irreducible] Code.splitItems

theorem row_primitive : Primrec₂ (fun args : Nat × Nat => Code.row args.1 args.2) := by
  have hs : Primrec (fun p : (Nat × Nat) × Code.RowData =>
      Code.splitItems p.1.1 p.1.2 p.2.2) :=
    splitItems_primitive.comp Primrec.fst (Primrec.snd.comp Primrec.snd)
  exact (IntegerAlgorithms.Proof.add_primitive.comp
    (Primrec.fst.comp Primrec.snd) (Primrec.fst.comp hs)).pair (Primrec.snd.comp hs)

theorem fixedCutoff_primitive : Primrec₂ Code.fixedCutoff := by
  let I := Int × Code.ItemData
  let A := Nat × Code.RowData
  have hi : Primrec (fun p : A × (I × Nat) => p.1.1) :=
    Primrec.fst.comp Primrec.fst
  have ha : Primrec (fun p : A × (I × Nat) => p.2.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.snd)
  have hs : Primrec (fun p : A × (I × Nat) =>
      max (if p.2.1.2.2.1 = p.1.1 then NormalForm.Code.itemCutoff p.2.1.2 else 0) p.2.2) :=
    Primrec.nat_max.comp
      (Primrec.ite (Primrec.eq.comp (item_name_primitive.comp ha) hi)
        (NormalFormCodeProof.itemCutoff_primitive.comp ha) (Primrec.const 0))
      (Primrec.snd.comp Primrec.snd)
  exact Primrec.list_foldr (Primrec.snd.comp Primrec.snd) (Primrec.const 0) hs.to₂

attribute [local irreducible] Code.row

theorem atom_primitive : Primrec₂ (fun args : Nat × Nat => Code.atom args.1 args.2) :=
  (Primrec.fst.comp Primrec.snd).pair
    ((Primrec.fst.comp (Primrec.snd.comp Primrec.snd)).pair
      (row_primitive.comp Primrec.fst (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))

attribute [local irreducible] Code.atom

private def formulaChildren (code : Nat) : List Nat :=
  if code % 6 = 0 ∨ code % 6 = 1 ∨ code % 6 = 2 then []
  else if code % 6 = 3 then [code / 6]
  else [(code / 6).unpair.1, (code / 6).unpair.2]

private def formulaAssemble (args : Nat × Nat) (code : Nat) (values : List Nat) : Nat :=
  if code % 6 = 0 then 0
  else if code % 6 = 1 then 1
  else if code % 6 = 2 then 6 * Encodable.encode (Code.atom args.1 args.2
    ((Encodable.decode (code / 6) : Option Code.AtomData).getD (0, 0, (0 : Int), []))) + 2
  else if code % 6 = 3 then 6 * values.getD 0 0 + 3
  else 6 * Nat.pair (values.getD 0 0) (values.getD 1 0) + code % 6

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

private theorem formula_equation (args : Nat × Nat) (code : Nat) :
    Code.formula args.1 args.2 code =
      formulaAssemble args code ((formulaChildren code).map (Code.formula args.1 args.2)) := by
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

private theorem formulaAssemble_primitive :
    Primrec (fun p : (Nat × Nat) × (Nat × List Nat) => formulaAssemble p.1 p.2.1 p.2.2) := by
  let A := (Nat × Nat) × (Nat × List Nat)
  have hc : Primrec (fun p : A => p.2.1) := Primrec.fst.comp Primrec.snd
  have hv : Primrec (fun p : A => p.2.2) := Primrec.snd.comp Primrec.snd
  have hd : Primrec (fun p : A =>
      (Encodable.decode (p.2.1 / 6) : Option Code.AtomData).getD (0, 0, (0 : Int), [])) :=
    Primrec.option_getD.comp
      ((Primrec.decode : Primrec (fun n : Nat => (Encodable.decode n : Option Code.AtomData))).comp
        (quotient_primitive.comp hc))
      (Primrec.const (0, 0, (0 : Int), []))
  have h0 : Primrec (fun p : A => p.2.2.getD 0 0) :=
    (Primrec.list_getD (0 : Nat)).comp hv (Primrec.const 0)
  have h1 : Primrec (fun p : A => p.2.2.getD 1 0) :=
    (Primrec.list_getD (0 : Nat)).comp hv (Primrec.const 1)
  have hatom : Primrec (fun p : A => 6 * Encodable.encode (Code.atom p.1.1 p.1.2
      ((Encodable.decode (p.2.1 / 6) : Option Code.AtomData).getD (0, 0, (0 : Int), []))) + 2) :=
    (unary_primitive 2).comp (Primrec.encode.comp (atom_primitive.comp Primrec.fst hd))
  have hb : Primrec (fun p : A =>
      6 * Nat.pair (p.2.2.getD 0 0) (p.2.2.getD 1 0) + p.2.1 % 6) :=
    Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 6) (Primrec₂.natPair.comp h0 h1))
      (tag_primitive.comp hc)
  exact Primrec.ite ((tag_is 0).comp hc) (Primrec.const 0)
    (Primrec.ite ((tag_is 1).comp hc) (Primrec.const 1)
      (Primrec.ite ((tag_is 2).comp hc) hatom
        (Primrec.ite ((tag_is 3).comp hc) ((unary_primitive 3).comp h0) hb)))

private def formulaStep (args : Nat × Nat) (values : List Nat) : Option Nat :=
  some (formulaAssemble args values.length
    ((formulaChildren values.length).map (fun i => values.getD i 0)))

private theorem formulaStep_primitive : Primrec₂ formulaStep := by
  let A := (Nat × Nat) × List Nat
  have hs : Primrec (fun p : A × Nat => p.1.2.getD p.2 0) :=
    (Primrec.list_getD (0 : Nat)).comp (Primrec.snd.comp Primrec.fst) Primrec.snd
  have hm : Primrec (fun p : A =>
      (formulaChildren p.2.length).map (fun i => p.2.getD i 0)) :=
    Primrec.list_map
      (formulaChildren_primitive.comp (Primrec.list_length.comp Primrec.snd)) hs.to₂
  have hp : Primrec (fun p : A =>
      (p.1, p.2.length, (formulaChildren p.2.length).map (fun i => p.2.getD i 0))) :=
    Primrec.fst.pair ((Primrec.list_length.comp Primrec.snd).pair hm)
  exact Primrec.option_some.comp (formulaAssemble_primitive.comp hp)

/-- Course-of-values recursion retains the substituted name and value in every
recursive call and handles every numeric code, including malformed atom data. -/
theorem formula_primitive :
    Primrec₂ (fun args : Nat × Nat => Code.formula args.1 args.2) := by
  apply Primrec.nat_strong_rec _ formulaStep_primitive
  intro args code
  unfold formulaStep
  simp only [List.length_map, List.length_range]
  apply congrArg some
  rw [formula_equation args code]
  apply congrArg (formulaAssemble args code)
  apply List.map_congr_left
  intro i hi
  have hlt := formula_decreasing code i hi
  simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hlt]

theorem any_primitive : Primrec Code.any := by
  have hs : Primrec (fun p : List Nat × (Nat × Nat) => 6 * Nat.pair p.2.1 p.2.2 + 5) :=
    (binary_primitive 5).comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
  exact Primrec.list_foldr Primrec.id (Primrec.const 1) hs.to₂

theorem bounded_primitive : Primrec₂ (fun args : Nat × Nat => Code.bounded args.1 args.2) := by
  let A := (Nat × Nat) × Nat
  have hs : Primrec (fun p : A × Nat => Code.formula p.1.1.1 p.2 p.1.2) :=
    formula_primitive.comp
      ((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair Primrec.snd)
      (Primrec.snd.comp Primrec.fst)
  have hm : Primrec (fun p : A =>
      (List.range p.1.2).map (fun n => Code.formula p.1.1 n p.2)) :=
    Primrec.list_map
      (Primrec.list_range.comp (Primrec.snd.comp Primrec.fst)) hs.to₂
  exact any_primitive.comp hm

attribute [local irreducible] Code.bounded

theorem block_primitive : Primrec₂ Code.block := by
  have hs : Primrec (fun p : (List (Nat × Nat) × Nat) × ((Nat × Nat) × Nat) =>
      Code.bounded p.2.1.1 p.2.1.2 p.2.2) :=
    bounded_primitive.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
  exact Primrec.list_foldr Primrec.fst Primrec.snd hs.to₂

theorem actualNumericPrograms : BoundedRowsTargets.ActualNumericPrograms :=
  ⟨itemValue_primitive, row_primitive, fixedCutoff_primitive,
    formula_primitive, bounded_primitive, block_primitive⟩

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BoundedRowsCodeProof
