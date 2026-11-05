module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceBooleanProgramsDataProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceBooleanProgramsProof
open SourceBooleanPrograms
attribute [local irreducible] Nat.sqrt Nat.unpair Code.shift Code.count

private def children (code : Nat) : List Nat :=
  if code % 5 = 0 ∨ code % 5 = 1 then []
  else if code % 5 = 2 then [code / 5]
  else if code % 5 = 3 then [(code / 5).unpair.1, (code / 5).unpair.2]
  else [(code / 5).unpair.2]

private theorem children_decreasing : ∀ code child, child ∈ children code → child < code := by
  intro code child h
  by_cases hleaf : code % 5 = 0 ∨ code % 5 = 1
  · simp [children, hleaf] at h
  have hpos : 0 < code := by omega
  have hd : code / 5 < code := Nat.div_lt_self hpos (by decide)
  have hl := Nat.unpair_left_le (code / 5)
  have hr := Nat.unpair_right_le (code / 5)
  unfold children at h
  split_ifs at h <;> simp_all only [List.mem_cons, List.not_mem_nil, or_false]
  all_goals omega

private def assemble (code : Nat) (values : List Code.Payload) : Code.Payload :=
  if code % 5 = 0 ∨ code % 5 = 1 then
    let a := (code / 5).unpair.1
    let b := (code / 5).unpair.2
    (true, 4 * Nat.pair a b + 2,
      SourceRows.Code.relation (code % 5 == 1) (Code.count a - 1) (Code.count a + Code.count b - 1))
  else if code % 5 = 2 then
    let p := values.getD 0 (false, 0, 0)
    (p.1, p.2.1, 6 * p.2.2 + 3)
  else if code % 5 = 3 then
    let p := values.getD 0 (false, 0, 0)
    let q := values.getD 1 (false, 0, 0)
    (p.1 && q.1, 4 * Nat.pair p.2.1 q.2.1 + 2,
      6 * Nat.pair p.2.2 (Code.shift (Code.count p.2.1) q.2.2) + 4)
  else (false, (values.getD 0 (false, 0, 0)).2.1, 1)

private theorem payload_equation (code : Nat) :
    Code.payload code = assemble code ((children code).map Code.payload) := by
  rw [Code.payload]
  split_ifs <;> simp_all [children, assemble]

private theorem tag_primitive : Primrec (fun code : Nat => code % 5) :=
  Primrec.nat_mod.comp Primrec.id (Primrec.const 5)
private theorem quotient_primitive : Primrec (fun code : Nat => code / 5) :=
  Primrec.nat_div.comp Primrec.id (Primrec.const 5)
private theorem tag_is (n : Nat) : PrimrecPred (fun code : Nat => code % 5 = n) :=
  Primrec.eq.comp tag_primitive (Primrec.const n)
private theorem left_primitive : Primrec (fun code : Nat => (code / 5).unpair.1) :=
  Primrec.fst.comp (Primrec.unpair.comp quotient_primitive)
private theorem right_primitive : Primrec (fun code : Nat => (code / 5).unpair.2) :=
  Primrec.snd.comp (Primrec.unpair.comp quotient_primitive)
private theorem children_primitive : Primrec children :=
  Primrec.ite ((tag_is 0).or (tag_is 1)) (Primrec.const [])
    (Primrec.ite (tag_is 2)
      (Primrec.list_cons.comp quotient_primitive (Primrec.const []))
      (Primrec.ite (tag_is 3)
        (Primrec.list_cons.comp left_primitive (Primrec.list_cons.comp right_primitive (Primrec.const [])))
        (Primrec.list_cons.comp right_primitive (Primrec.const []))))

private theorem assemble_primitive : Primrec₂ assemble := by
  let A := Nat × List Code.Payload
  have h0 : Primrec (fun p : A => p.2.getD 0 (false, 0, 0)) :=
    (Primrec.list_getD (false, 0, 0)).comp Primrec.snd (Primrec.const 0)
  have h1 : Primrec (fun p : A => p.2.getD 1 (false, 0, 0)) :=
    (Primrec.list_getD (false, 0, 0)).comp Primrec.snd (Primrec.const 1)
  have ha : Primrec (fun p : A => (p.1 / 5).unpair.1) := left_primitive.comp Primrec.fst
  have hb : Primrec (fun p : A => (p.1 / 5).unpair.2) := right_primitive.comp Primrec.fst
  have hc : Primrec (fun p : A => Code.count (p.1 / 5).unpair.1) := count_primitive.comp ha
  have hd : Primrec (fun p : A => Code.count (p.1 / 5).unpair.2) := count_primitive.comp hb
  have hstrict : Primrec (fun p : A => p.1 % 5 == 1) := by
    apply (((tag_is 1).comp Primrec.fst).decide).of_eq
    intro p
    by_cases h : p.1 % 5 = 1 <;> simp [h]
  have hrel := SourceRowsCodeProof.relation_primitive.comp
    (hstrict.pair ((Primrec.nat_sub.comp hc (Primrec.const 1)).pair
      (Primrec.nat_sub.comp (Primrec.nat_add.comp hc hd) (Primrec.const 1))))
  have hleaf : Primrec (fun p : A => (true, 4 * Nat.pair (p.1 / 5).unpair.1 (p.1 / 5).unpair.2 + 2,
      SourceRows.Code.relation (p.1 % 5 == 1) (Code.count (p.1 / 5).unpair.1 - 1)
        (Code.count (p.1 / 5).unpair.1 + Code.count (p.1 / 5).unpair.2 - 1))) :=
    (Primrec.const true).pair (((binary_primitive 4 2).comp ha hb).pair hrel)
  have hf0 := Primrec.fst.comp (Primrec.snd.comp h0)
  have hf1 := Primrec.fst.comp (Primrec.snd.comp h1)
  have hp0 := Primrec.snd.comp (Primrec.snd.comp h0)
  have hp1 := Primrec.snd.comp (Primrec.snd.comp h1)
  have hneg := (Primrec.fst.comp h0).pair (hf0.pair ((unary_primitive 6 3).comp hp0))
  have hconj := (Primrec.and.comp (Primrec.fst.comp h0) (Primrec.fst.comp h1)).pair
    (((binary_primitive 4 2).comp hf0 hf1).pair
      ((binary_primitive 6 4).comp hp0 (shift_primitive.comp (count_primitive.comp hf0) hp1)))
  have hex := (Primrec.const false).pair (hf0.pair (Primrec.const 1))
  exact Primrec.ite (((tag_is 0).or (tag_is 1)).comp Primrec.fst) hleaf
    (Primrec.ite ((tag_is 2).comp Primrec.fst) hneg
      (Primrec.ite ((tag_is 3).comp Primrec.fst) hconj hex))

private def step (values : List Code.Payload) : Option Code.Payload :=
  some (assemble values.length ((children values.length).map (fun i => values.getD i (false, 0, 0))))

private theorem step_primitive : Primrec step := by
  have hs : Primrec (fun p : List Code.Payload × Nat => p.1.getD p.2 (false, 0, 0)) :=
    (Primrec.list_getD (false, 0, 0)).comp Primrec.fst Primrec.snd
  have hm : Primrec (fun values : List Code.Payload =>
      (children values.length).map (fun i => values.getD i (false, 0, 0))) :=
    Primrec.list_map (children_primitive.comp Primrec.list_length) hs.to₂
  exact Primrec.option_some.comp (assemble_primitive.comp Primrec.list_length hm)

theorem payload_primitive : Primrec Code.payload := by
  have h : Primrec₂ (fun (_ : Unit) code => Code.payload code) := by
    apply Primrec.nat_strong_rec _ (step_primitive.comp Primrec.snd).to₂
    intro _ code
    unfold step
    simp only [List.length_map, List.length_range]
    apply congrArg some
    rw [payload_equation code]
    apply congrArg (assemble code)
    apply List.map_congr_left
    intro i hi
    have hlt := children_decreasing code i hi
    simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hlt]
  exact h.comp (Primrec.const ()) Primrec.id

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceBooleanProgramsProof
