module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SignedRowsTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BoundedRowsCodeProgramsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SignedRowsCodeProof
open SignedRows
attribute [local irreducible] Nat.sqrt Nat.unpair

private theorem binary_primitive (tag : Nat) :
    Primrec₂ (fun a b : Nat => 6 * Nat.pair a b + tag) :=
  Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 6) Primrec₂.natPair)
    (Primrec.const tag)
private theorem unary_primitive (tag : Nat) :
    Primrec (fun a : Nat => 6 * a + tag) :=
  Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 6) Primrec.id)
    (Primrec.const tag)
private theorem input_left : Primrec (fun p : Code.Input => p.1.1) :=
  Primrec.fst.comp Primrec.fst
private theorem input_right : Primrec (fun p : Code.Input => p.1.2) :=
  Primrec.snd.comp Primrec.fst
private theorem input_shift : Primrec (fun p : Code.Input => p.2) := Primrec.snd
private theorem item_tag : Primrec (fun s : Code.ItemData => s.1) := Primrec.fst
private theorem item_name : Primrec (fun s : Code.ItemData => s.2.1) :=
  Primrec.fst.comp Primrec.snd
private theorem item_index : Primrec (fun s : Code.ItemData => s.2.2.1) :=
  Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
private theorem item_outer : Primrec (fun s : Code.ItemData => s.2.2.2) :=
  Primrec.snd.comp (Primrec.snd.comp Primrec.snd)

theorem item_primitive :
    Primrec₂ (fun args : Code.Input => Code.item args.1.1 args.1.2 args.2) := by
  let A := Code.Input × Code.ItemData
  have hj : Primrec (fun p : A => p.1.1.2) := input_right.comp Primrec.fst
  have he : Primrec (fun p : A => p.1.2 + p.2.2.2.1) :=
    IntegerAlgorithms.Proof.add_primitive.comp
      (input_shift.comp Primrec.fst) (item_index.comp Primrec.snd)
  have hv : Primrec (fun p : A => ((0, p.1.1.2, 0, 0) : Code.ItemData)) :=
    (Primrec.const 0).pair (hj.pair ((Primrec.const (0 : Int)).pair (Primrec.const (0 : Int))))
  have hp : Primrec (fun p : A => ((1, p.1.1.2, p.1.2 + p.2.2.2.1, 0) : Code.ItemData)) :=
    (Primrec.const 1).pair (hj.pair (he.pair (Primrec.const (0 : Int))))
  have hh : Primrec (fun p : A =>
      ((2, p.1.1.2, p.1.2 + p.2.2.2.1, p.2.2.2.2) : Code.ItemData)) :=
    (Primrec.const 2).pair (hj.pair (he.pair (item_outer.comp Primrec.snd)))
  exact Primrec.ite
    (Primrec.eq.comp (item_name.comp Primrec.snd) (input_left.comp Primrec.fst))
    (Primrec.ite (Primrec.eq.comp (item_tag.comp Primrec.snd) (Primrec.const 0)) hv
      (Primrec.ite (Primrec.eq.comp (item_tag.comp Primrec.snd) (Primrec.const 1)) hp hh))
    Primrec.snd

theorem offset_primitive :
    Primrec₂ (fun args : Nat × Int => Code.offset args.1 args.2) :=
  Primrec.ite
    (Primrec.eq.comp (item_name.comp Primrec.snd) (Primrec.fst.comp Primrec.fst))
    (Primrec.ite (Primrec.eq.comp (item_tag.comp Primrec.snd) (Primrec.const 0))
      (Primrec.snd.comp Primrec.fst) (Primrec.const (0 : Int)))
    (Primrec.const (0 : Int))

attribute [local irreducible] Code.item Code.offset

private theorem integerSum_primitive : Primrec (fun xs : List Int => xs.sum) := by
  have hs : Primrec (fun p : List Int × (Int × Int) => p.2.1 + p.2.2) :=
    IntegerAlgorithms.Proof.add_primitive.comp
      (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
  have hf : Primrec (fun xs : List Int => xs.foldr (fun a b => a + b) 0) :=
    Primrec.list_foldr Primrec.id (Primrec.const (0 : Int)) hs.to₂
  apply hf.of_eq
  intro xs
  induction xs with
  | nil => rfl
  | cons a xs ih => simp only [List.foldr_cons, List.sum_cons, ih]

theorem row_primitive :
    Primrec₂ (fun args : Code.Input => Code.row args.1.1 args.1.2 args.2) := by
  let I := Int × Code.ItemData
  let A := Code.Input × Code.RowData
  have hargs : Primrec (fun p : A × I => p.1.1) := Primrec.fst.comp Primrec.fst
  have hw : Primrec (fun p : A × I => p.2.1) := Primrec.fst.comp Primrec.snd
  have hs : Primrec (fun p : A × I => p.2.2) := Primrec.snd.comp Primrec.snd
  have hvalue : Primrec (fun p : A × I =>
      p.2.1 * Code.offset p.1.1.1.1 p.1.1.2 p.2.2) :=
    IntegerAlgorithms.Proof.mul_primitive.comp hw
      (offset_primitive.comp ((input_left.comp hargs).pair (input_shift.comp hargs)) hs)
  have hvalues : Primrec (fun p : A =>
      p.2.2.map (fun a => a.1 * Code.offset p.1.1.1 p.1.2 a.2)) :=
    Primrec.list_map (Primrec.snd.comp Primrec.snd) hvalue.to₂
  have hitem : Primrec (fun p : A × I =>
      (p.2.1, Code.item p.1.1.1.1 p.1.1.1.2 p.1.1.2 p.2.2)) :=
    hw.pair (item_primitive.comp hargs hs)
  have hitems : Primrec (fun p : A =>
      p.2.2.map (fun a => (a.1, Code.item p.1.1.1 p.1.1.2 p.1.2 a.2))) :=
    Primrec.list_map (Primrec.snd.comp Primrec.snd) hitem.to₂
  exact (IntegerAlgorithms.Proof.add_primitive.comp
    (Primrec.fst.comp Primrec.snd) (integerSum_primitive.comp hvalues)).pair hitems

attribute [local irreducible] Code.row

theorem atom_primitive :
    Primrec₂ (fun args : Code.Input => Code.atom args.1.1 args.1.2 args.2) :=
  (Primrec.fst.comp Primrec.snd).pair
    ((Primrec.fst.comp (Primrec.snd.comp Primrec.snd)).pair
      (row_primitive.comp Primrec.fst (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))

attribute [local irreducible] Code.atom

private def coreChildren (code : Nat) : List Nat :=
  if code % 6 = 0 ∨ code % 6 = 1 ∨ code % 6 = 2 then []
  else if code % 6 = 3 then [code / 6]
  else [(code / 6).unpair.1, (code / 6).unpair.2]

private def coreAssemble (args : Code.Input) (code : Nat) (values : List Nat) : Nat :=
  if code % 6 = 0 then 0
  else if code % 6 = 1 then 1
  else if code % 6 = 2 then 6 * Encodable.encode (Code.atom args.1.1 args.1.2 args.2
    ((Encodable.decode (code / 6) : Option Code.AtomData).getD (0, 0, (0 : Int), []))) + 2
  else if code % 6 = 3 then 6 * values.getD 0 0 + 3
  else 6 * Nat.pair (values.getD 0 0) (values.getD 1 0) + code % 6

private theorem core_decreasing : ∀ code child, child ∈ coreChildren code → child < code := by
  intro code child h
  by_cases hleaf : code % 6 = 0 ∨ code % 6 = 1 ∨ code % 6 = 2
  · simp [coreChildren, hleaf] at h
  have hpos : 0 < code := by omega
  have hd : code / 6 < code := Nat.div_lt_self hpos (by decide)
  have hl := Nat.unpair_left_le (code / 6)
  have hr := Nat.unpair_right_le (code / 6)
  unfold coreChildren at h
  split_ifs at h <;> simp_all only [List.mem_cons, List.not_mem_nil, or_false]
  all_goals omega

private theorem core_equation (args : Code.Input) (code : Nat) :
    Code.core args.1.1 args.1.2 args.2 code =
      coreAssemble args code ((coreChildren code).map (Code.core args.1.1 args.1.2 args.2)) := by
  rw [Code.core]
  split_ifs <;> simp_all [coreChildren, coreAssemble]

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
private theorem coreChildren_primitive : Primrec coreChildren :=
  Primrec.ite ((tag_is 0).or ((tag_is 1).or (tag_is 2))) (Primrec.const [])
    (Primrec.ite (tag_is 3)
      (Primrec.list_cons.comp quotient_primitive (Primrec.const []))
      (Primrec.list_cons.comp left_primitive
        (Primrec.list_cons.comp right_primitive (Primrec.const []))))

private theorem coreAssemble_primitive :
    Primrec (fun p : Code.Input × (Nat × List Nat) => coreAssemble p.1 p.2.1 p.2.2) := by
  let A := Code.Input × (Nat × List Nat)
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
  have hatom : Primrec (fun p : A => 6 * Encodable.encode (Code.atom p.1.1.1 p.1.1.2 p.1.2
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

private def coreStep (args : Code.Input) (values : List Nat) : Option Nat :=
  some (coreAssemble args values.length
    ((coreChildren values.length).map (fun i => values.getD i 0)))

private theorem coreStep_primitive : Primrec₂ coreStep := by
  let A := Code.Input × List Nat
  have hs : Primrec (fun p : A × Nat => p.1.2.getD p.2 0) :=
    (Primrec.list_getD (0 : Nat)).comp (Primrec.snd.comp Primrec.fst) Primrec.snd
  have hm : Primrec (fun p : A =>
      (coreChildren p.2.length).map (fun i => p.2.getD i 0)) :=
    Primrec.list_map
      (coreChildren_primitive.comp (Primrec.list_length.comp Primrec.snd)) hs.to₂
  have hp : Primrec (fun p : A =>
      (p.1, p.2.length, (coreChildren p.2.length).map (fun i => p.2.getD i 0))) :=
    Primrec.fst.pair ((Primrec.list_length.comp Primrec.snd).pair hm)
  exact Primrec.option_some.comp (coreAssemble_primitive.comp hp)

theorem core_primitive :
    Primrec₂ (fun args : Code.Input => Code.core args.1.1 args.1.2 args.2) := by
  apply Primrec.nat_strong_rec _ coreStep_primitive
  intro args code
  unfold coreStep
  simp only [List.length_map, List.length_range]
  apply congrArg some
  rw [core_equation args code]
  apply congrArg (coreAssemble args code)
  apply List.map_congr_left
  intro i hi
  have hlt := core_decreasing code i hi
  simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hlt]

theorem anchorDomain_primitive : Primrec₂ Code.anchorDomain := by
  let A := Nat × Int
  have hv : Primrec (fun p : A => ((0, p.1, 0, 0) : Code.ItemData)) :=
    (Primrec.const 0).pair (Primrec.fst.pair
      ((Primrec.const (0 : Int)).pair (Primrec.const (0 : Int))))
  have hl : Primrec (fun p : A => [((1 : Int), ((0, p.1, 0, 0) : Code.ItemData))]) :=
    Primrec.list_cons.comp ((Primrec.const (1 : Int)).pair hv) (Primrec.const [])
  have ha : Primrec (fun p : A =>
      ((0, 0, p.2, [(1, (0, p.1, 0, 0))]) : Code.AtomData)) :=
    (Primrec.const 0).pair ((Primrec.const 0).pair (Primrec.snd.pair hl))
  exact (unary_primitive 2).comp (Primrec.encode.comp ha)

attribute [local irreducible] Code.anchorDomain

theorem substitute_primitive :
    Primrec₂ (fun args : Code.Input => Code.substitute args.1.1 args.1.2 args.2) := by
  let A := Code.Input × Nat
  have hd : Primrec (fun p : A => Code.anchorDomain p.1.1.2 p.1.2) :=
    anchorDomain_primitive.comp (input_right.comp Primrec.fst) (input_shift.comp Primrec.fst)
  have hz : Primrec (fun p : A => BoundedRows.Code.formula p.1.1.1 0 p.2) :=
    BoundedRowsCodeProof.formula_primitive.comp
      ((input_left.comp Primrec.fst).pair (Primrec.const 0)) Primrec.snd
  exact (binary_primitive 5).comp ((binary_primitive 4).comp hd core_primitive)
    ((binary_primitive 4).comp ((unary_primitive 3).comp hd) hz)

theorem actualNumericPrograms : SignedRowsTargets.ActualNumericPrograms :=
  ⟨item_primitive, offset_primitive, row_primitive, core_primitive, substitute_primitive⟩

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SignedRowsCodeProof
