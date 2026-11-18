module
public import LogicLineages.StandardControlCurrent.OrderedOccurrenceRawDefinitions
public import Mathlib.Computability.Primrec.List
public import Mathlib.Tactic.SplitIfs
@[expose] public section
namespace LogicLineages.StandardControlCurrent.OrderedOccurrenceRaw
open OrdinalComparison LayeredComparison.SnyatkovCompletion NormalForm
attribute [local irreducible] Nat.sqrt Nat.unpair

def rowsChildren (code : Nat) : List Nat :=
  if code % 6 = 0 ∨ code % 6 = 1 ∨ code % 6 = 2 then []
  else if code % 6 = 3 then [code / 6]
  else [(code / 6).unpair.1,(code / 6).unpair.2]
def rowsAssemble (code : Nat) (values : List (List Code.RowData)) : List Code.RowData :=
  if code % 6 = 0 then []
  else if code % 6 = 1 then []
  else if code % 6 = 2 then
    [((Encodable.decode (code / 6) : Option Code.AtomData).getD (0,0,0,[])).2.2]
  else if code % 6 = 3 then values.getD 0 []
  else values.getD 0 [] ++ values.getD 1 []

theorem rows_equation (code : Nat) : rows code=rowsAssemble code ((rowsChildren code).map rows) := by
  rw [rows]
  unfold rowsAssemble rowsChildren
  split_ifs <;> simp_all <;> omega

theorem rows_decreasing : ∀ code child, child ∈ rowsChildren code → child < code := by
  intro code child h
  by_cases hleaf : code % 6 = 0 ∨ code % 6 = 1 ∨ code % 6 = 2
  · simp [rowsChildren, hleaf] at h
  have hpos : 0 < code := by omega
  have hd : code / 6 < code := Nat.div_lt_self hpos (by decide)
  have hl := Nat.unpair_left_le (code / 6)
  have hr := Nat.unpair_right_le (code / 6)
  unfold rowsChildren at h
  split_ifs at h <;> simp_all only [List.mem_cons, List.not_mem_nil, or_false]
  all_goals omega

theorem tag_primitive : Primrec (fun code : Nat => code % 6) :=
  Primrec.nat_mod.comp Primrec.id (Primrec.const 6)
theorem quotient_primitive : Primrec (fun code : Nat => code / 6) :=
  Primrec.nat_div.comp Primrec.id (Primrec.const 6)
theorem tag_is (n : Nat) : PrimrecPred (fun code : Nat => code % 6 = n) :=
  Primrec.eq.comp tag_primitive (Primrec.const n)
theorem left_primitive : Primrec (fun code : Nat => (code / 6).unpair.1) :=
  Primrec.fst.comp (Primrec.unpair.comp quotient_primitive)
theorem right_primitive : Primrec (fun code : Nat => (code / 6).unpair.2) :=
  Primrec.snd.comp (Primrec.unpair.comp quotient_primitive)
theorem rowsChildren_primitive : Primrec rowsChildren :=
  Primrec.ite ((tag_is 0).or ((tag_is 1).or (tag_is 2))) (Primrec.const [])
    (Primrec.ite (tag_is 3)
      (Primrec.list_cons.comp quotient_primitive (Primrec.const []))
      (Primrec.list_cons.comp left_primitive
        (Primrec.list_cons.comp right_primitive (Primrec.const []))))


theorem rowsAssemble_primitive : Primrec₂ rowsAssemble := by
  let A := Nat × List (List Code.RowData)
  have hd : Primrec (fun p : A =>
      (Encodable.decode (p.1 / 6) : Option Code.AtomData).getD (0,0,0,[])) :=
    Primrec.option_getD.comp
      ((Primrec.decode : Primrec (fun n : Nat => (Encodable.decode n : Option Code.AtomData))).comp
        (quotient_primitive.comp Primrec.fst)) (Primrec.const (0,0,0,[]))
  have h0 : Primrec (fun p : A => p.2.getD 0 []) :=
    (Primrec.list_getD ([] : List Code.RowData)).comp Primrec.snd (Primrec.const 0)
  have h1 : Primrec (fun p : A => p.2.getD 1 []) :=
    (Primrec.list_getD ([] : List Code.RowData)).comp Primrec.snd (Primrec.const 1)
  exact Primrec.ite ((tag_is 0).comp Primrec.fst) (Primrec.const [])
    (Primrec.ite ((tag_is 1).comp Primrec.fst) (Primrec.const [])
      (Primrec.ite ((tag_is 2).comp Primrec.fst)
        (Primrec.list_cons.comp (Primrec.snd.comp (Primrec.snd.comp hd)) (Primrec.const []))
        (Primrec.ite ((tag_is 3).comp Primrec.fst) h0 (Primrec.list_append.comp h0 h1))))

private def rowsStep (values : List (List Code.RowData)) : Option (List Code.RowData) :=
  some (rowsAssemble values.length ((rowsChildren values.length).map (fun i => values.getD i [])))
private theorem rowsStep_primitive : Primrec rowsStep := by
  have hs : Primrec (fun p : List (List Code.RowData) × Nat => p.1.getD p.2 []) :=
    (Primrec.list_getD ([] : List Code.RowData)).comp Primrec.fst Primrec.snd
  have hm : Primrec (fun values : List (List Code.RowData) =>
      (rowsChildren values.length).map (fun i => values.getD i [])) :=
    Primrec.list_map (rowsChildren_primitive.comp Primrec.list_length) hs.to₂
  exact Primrec.option_some.comp (rowsAssemble_primitive.comp Primrec.list_length hm)

theorem rows_primitive : Primrec rows := by
  have h : Primrec₂ (fun (_ : Unit) (code : Nat) => rows code) := by
    apply Primrec.nat_strong_rec _ (rowsStep_primitive.comp Primrec.snd).to₂
    intro _ code
    unfold rowsStep
    simp only [List.length_map,List.length_range]
    apply congrArg some
    rw [rows_equation code]
    apply congrArg (rowsAssemble code)
    apply List.map_congr_left
    intro i hi
    have hlt := rows_decreasing code i hi
    simp [List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range hlt]
  exact h.comp (Primrec.const ()) Primrec.id
end LogicLineages.StandardControlCurrent.OrderedOccurrenceRaw
