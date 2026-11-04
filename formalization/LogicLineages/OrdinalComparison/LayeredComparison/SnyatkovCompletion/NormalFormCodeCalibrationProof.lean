module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NormalFormTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NormalFormCodeProof
open NormalForm

/-- Literal code calibration retains every occurrence, including zero weights. -/
theorem item_term (s : Summand) : Code.itemTerm s.data = s.term.encode := by
  cases s <;> rfl

theorem item_cutoff (s : Summand) : Code.itemCutoff s.data = s.domainCutoff := by
  cases s <;> rfl

private theorem positive_fold (xs : List (Int × Summand)) :
    (xs.map (fun a => (a.1, a.2.data))).foldr
      (fun a rest => WindowCode.add
        (WindowCode.multiply a.1.toNat (Code.itemTerm a.2)) rest) (WindowCode.numeral 0) =
      (xs.foldr (fun a rest => Term.add (.multiply a.1.toNat a.2.term) rest)
        (.numeral 0)).encode := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      simp only [List.map_cons, List.foldr_cons, Term.encode]
      rw [item_term, ih]
      rfl

private theorem negative_fold (xs : List (Int × Summand)) :
    (xs.map (fun a => (a.1, a.2.data))).foldr
      (fun a rest => WindowCode.add
        (WindowCode.multiply (-a.1).toNat (Code.itemTerm a.2)) rest) (WindowCode.numeral 0) =
      (xs.foldr (fun a rest => Term.add (.multiply (-a.1).toNat a.2.term) rest)
        (.numeral 0)).encode := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      simp only [List.map_cons, List.foldr_cons, Term.encode]
      rw [item_term, ih]
      rfl

theorem positive_calibration (row : Row) :
    Code.part false (rowData row) = (positiveTerm row).encode := by
  unfold Code.part Code.scalarPart rowData positiveTerm
  simp only [Bool.false_eq_true, ite_false, Term.encode]
  rw [positive_fold]
  rfl

theorem negative_calibration (row : Row) :
    Code.part true (rowData row) = (negativeTerm row).encode := by
  unfold Code.part Code.scalarPart rowData negativeTerm
  simp only [ite_true, Term.encode]
  rw [negative_fold]
  rfl

theorem absolute_calibration (row : Row) :
    Code.absolute (rowData row) = (absoluteTerm row).encode := by
  unfold Code.absolute absoluteTerm
  rw [positive_calibration, negative_calibration]
  rfl

theorem domain_data (s : Summand) :
    Code.domainRowData s.data = rowData (domainRow s) := by
  cases s <;> rfl

theorem atom_calibration (a : Atom) : Code.atom a.data = a.compile.encode := by
  cases a with
  | nonnegative row =>
      change Code.nonnegative (rowData row) = _
      unfold Code.nonnegative
      rw [negative_calibration, positive_calibration]
      rfl
  | divisible m row =>
      change Code.divisible m (rowData row) = _
      unfold Code.divisible
      rw [absolute_calibration]
      rfl

theorem domains_calibration (row : Row) :
    Code.domains (rowData row) = (domainFormula row).compile.encode := by
  rcases row with ⟨z, xs⟩
  change (xs.map (fun a => (a.1, a.2.data))).foldr
    (fun a rest => WindowCode.conjunction (Code.nonnegative (Code.domainRowData a.2)) rest) 0 =
    (xs.foldr (fun a rest => Formula.conjunction (.atom (.nonnegative (domainRow a.2))) rest)
      .truth).compile.encode
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      simp only [List.map_cons, List.foldr_cons, Formula.compile, Matrix.encode]
      rw [domain_data, ih]
      change WindowCode.conjunction (Code.atom (Atom.nonnegative (domainRow a.2)).data) _ = _
      rw [atom_calibration]
      rfl

private theorem formula_step (n tag : Nat) (ht : tag < 6) :
    Code.formula (6 * n + tag) =
      if tag = 0 then 0
      else if tag = 1 then 1
      else if tag = 2 then Code.atom
        ((Encodable.decode n : Option Code.AtomData).getD (0, 0, (0 : Int), []))
      else if tag = 3 then WindowCode.negative (Code.formula n)
      else 8 * Nat.pair (Code.formula n.unpair.1) (Code.formula n.unpair.2) + (tag + 2) := by
  have hm : (6 * n + tag) % 6 = tag := by omega
  have hd : (6 * n + tag) / 6 = n := by omega
  rw [Code.formula, hm, hd]

theorem formula_calibration (p : Formula) : Code.formula p.encode = p.compile.encode := by
  induction p with
  | truth =>
      simpa [Formula.encode, Formula.compile, Matrix.encode] using formula_step 0 0 (by decide)
  | falsity =>
      simpa [Formula.encode, Formula.compile, Matrix.encode] using formula_step 0 1 (by decide)
  | atom a =>
      change Code.formula (6 * Encodable.encode a.data + 2) = a.compile.encode
      have h := formula_step (Encodable.encode a.data) 2 (by decide)
      rw [if_neg (by decide : ¬(2 = (0 : Nat))),
        if_neg (by decide : ¬(2 = (1 : Nat))), if_pos rfl,
        Encodable.encodek] at h
      simpa only [Option.getD_some, atom_calibration] using h
  | negative p hp =>
      simpa [Formula.encode, Formula.compile, Matrix.encode, WindowCode.negative, hp] using
        formula_step p.encode 3 (by decide)
  | conjunction p q hp hq =>
      simpa [Formula.encode, Formula.compile, Matrix.encode, Nat.unpair_pair, hp, hq] using
        formula_step (Nat.pair p.encode q.encode) 4 (by decide)
  | disjunction p q hp hq =>
      simpa [Formula.encode, Formula.compile, Matrix.encode, Nat.unpair_pair, hp, hq] using
        formula_step (Nat.pair p.encode q.encode) 5 (by decide)

theorem literalCodeCalibration : NormalFormTargets.LiteralCodeCalibration :=
  ⟨fun s => ⟨item_term s, item_cutoff s⟩,
    fun row => ⟨positive_calibration row, negative_calibration row, domains_calibration row⟩,
    formula_calibration⟩

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NormalFormCodeProof
