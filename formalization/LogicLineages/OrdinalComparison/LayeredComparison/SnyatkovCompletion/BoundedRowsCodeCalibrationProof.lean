module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BoundedRowsTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NormalFormCodeCalibrationProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BoundedRowsCodeProof
open NormalForm (Summand Row rowData Atom Formula)
open BoundedRows

theorem itemValue_calibration (s : Summand) (n : Nat) :
    Code.itemValue s.data n = valueAt s n := by
  cases s <;> rfl

private theorem item_name (s : Summand) : s.data.2.1 = s.name := by
  cases s <;> rfl

private theorem split_cons (i n : Nat) (a : Int × Summand) (xs : List (Int × Summand)) :
    splitItems i n (a :: xs) = if a.2.name = i then
      (a.1 * (valueAt a.2 n : Int) + (splitItems i n xs).1, (splitItems i n xs).2)
    else ((splitItems i n xs).1, a :: (splitItems i n xs).2) := rfl

private theorem code_split_cons (i n : Nat) (a : Int × Code.ItemData)
    (xs : List (Int × Code.ItemData)) :
    Code.splitItems i n (a :: xs) = if a.2.2.1 = i then
      (a.1 * (Code.itemValue a.2 n : Int) + (Code.splitItems i n xs).1,
        (Code.splitItems i n xs).2)
    else ((Code.splitItems i n xs).1, a :: (Code.splitItems i n xs).2) := rfl

theorem splitItems_calibration (i n : Nat) (xs : List (Int × Summand)) :
    Code.splitItems i n (xs.map (fun a => (a.1, a.2.data))) =
      ((splitItems i n xs).1, (splitItems i n xs).2.map (fun a => (a.1, a.2.data))) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      simp only [List.map_cons, code_split_cons, split_cons, item_name, ih]
      by_cases h : a.2.name = i <;>
        simp only [h, ite_true, ite_false, itemValue_calibration, List.map_cons]

theorem row_calibration (i n : Nat) (row : Row) :
    Code.row i n (rowData row) = rowData (rowSubstitute i n row) := by
  unfold Code.row rowSubstitute rowData
  rw [splitItems_calibration]

theorem fixedCutoff_calibration (i : Nat) (row : Row) :
    Code.fixedCutoff i (rowData row) = fixedCutoff i row := by
  rcases row with ⟨z, xs⟩
  change (xs.map (fun a => (a.1, a.2.data))).foldr
    (fun a rest => max (if a.2.2.1 = i then NormalForm.Code.itemCutoff a.2 else 0) rest) 0 =
    xs.foldr (fun a rest => max (if a.2.name = i then a.2.domainCutoff else 0) rest) 0
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      simp only [List.map_cons, List.foldr_cons, item_name,
        NormalFormCodeProof.item_cutoff, ih]

theorem atom_calibration (i n : Nat) (a : Atom) :
    Code.atom i n a.data = (atomSubstitute i n a).data := by
  cases a <;> simp only [Code.atom, Atom.data, atomSubstitute, row_calibration]

private theorem formula_step (i n payload tag : Nat) (ht : tag < 6) :
    Code.formula i n (6 * payload + tag) =
      if tag = 0 then 0 else if tag = 1 then 1
      else if tag = 2 then 6 * Encodable.encode (Code.atom i n
        ((Encodable.decode payload : Option Code.AtomData).getD (0, 0, (0 : Int), []))) + 2
      else if tag = 3 then 6 * Code.formula i n payload + 3
      else 6 * Nat.pair (Code.formula i n payload.unpair.1)
        (Code.formula i n payload.unpair.2) + tag := by
  have hm : (6 * payload + tag) % 6 = tag := by omega
  have hd : (6 * payload + tag) / 6 = payload := by omega
  rw [Code.formula, hm, hd]

theorem formula_calibration (i n : Nat) (p : Formula) :
    Code.formula i n p.encode = (substitute i n p).encode := by
  induction p with
  | truth =>
      simpa [Formula.encode, substitute] using formula_step i n 0 0 (by decide)
  | falsity =>
      simpa [Formula.encode, substitute] using formula_step i n 0 1 (by decide)
  | atom a =>
      change Code.formula i n (6 * Encodable.encode a.data + 2) =
        6 * Encodable.encode (atomSubstitute i n a).data + 2
      have h := formula_step i n (Encodable.encode a.data) 2 (by decide)
      rw [if_neg (by decide : ¬(2 = (0 : Nat))),
        if_neg (by decide : ¬(2 = (1 : Nat))), if_pos rfl, Encodable.encodek] at h
      simpa only [Option.getD_some, atom_calibration] using h
  | negative p hp =>
      simpa [Formula.encode, substitute, hp] using formula_step i n p.encode 3 (by decide)
  | conjunction p q hp hq =>
      simpa [Formula.encode, substitute, Nat.unpair_pair, hp, hq] using
        formula_step i n (Nat.pair p.encode q.encode) 4 (by decide)
  | disjunction p q hp hq =>
      simpa [Formula.encode, substitute, Nat.unpair_pair, hp, hq] using
        formula_step i n (Nat.pair p.encode q.encode) 5 (by decide)

theorem any_calibration (ps : List Formula) :
    Code.any (ps.map Formula.encode) = (BoundedRows.any ps).encode := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
      change 6 * Nat.pair p.encode (Code.any (ps.map Formula.encode)) + 5 =
        6 * Nat.pair p.encode (BoundedRows.any ps).encode + 5
      rw [ih]

theorem bounded_calibration (i bound : Nat) (p : Formula) :
    Code.bounded i bound p.encode = (bounded i bound p).encode := by
  unfold Code.bounded bounded
  rw [← any_calibration]
  apply congrArg Code.any
  rw [List.map_map]
  apply List.map_congr_left
  intro n hn
  exact formula_calibration i n p

theorem block_calibration (bounds : List (Nat × Nat)) (p : Formula) :
    Code.block bounds p.encode = (block bounds p).encode := by
  induction bounds with
  | nil => rfl
  | cons entry rest ih =>
      change Code.bounded entry.1 entry.2 (Code.block rest p.encode) =
        (bounded entry.1 entry.2 (block rest p)).encode
      rw [ih, bounded_calibration]

theorem literalCodeCalibration : BoundedRowsTargets.LiteralCodeCalibration :=
  ⟨itemValue_calibration, fun i n row => ⟨row_calibration i n row, fixedCutoff_calibration i row⟩,
    formula_calibration, bounded_calibration, block_calibration⟩

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BoundedRowsCodeProof
