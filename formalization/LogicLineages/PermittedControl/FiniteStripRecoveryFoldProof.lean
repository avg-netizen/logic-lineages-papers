module
public import LogicLineages.PermittedControl.FiniteStripRecoveryTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BoundedRowsSemanticStatementChecks
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BoundedRowsCodeStatementChecks

@[expose] public section
namespace LogicLineages.PermittedControl.FiniteStripRecovery
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open NormalForm PreparedProjection

private theorem codePrimitive : Primrec₂ foldCode := by
  have hs : Primrec (fun p : (List (Nat × Nat) × Nat) × ((Nat × Nat) × Nat) =>
      BoundedRows.Code.formula p.2.1.1 p.2.1.2 p.2.2) :=
    BoundedRowsCodeProof.formula_primitive.comp
      (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
  exact Primrec.list_foldr Primrec.fst Primrec.snd hs.to₂

private theorem codeCalibration (reads : List (Nat × Nat)) (p : Formula) :
    foldCode reads p.encode = (foldFormula reads p).encode := by
  induction reads with
  | nil => rfl
  | cons r rs ih =>
    change BoundedRows.Code.formula r.1 r.2 (foldCode rs p.encode) = _
    rw [ih]
    exact BoundedRowsCodeStatementChecks.literal_code_calibration.2.2.1
      r.1 r.2 (foldFormula rs p)

theorem foldCodeExact : FoldCodeExact := ⟨codePrimitive,codeCalibration⟩

theorem foldActual : FoldActual := by
  intro reads p ν
  induction reads generalizing ν with
  | nil => rfl
  | cons r rs ih =>
    exact (BoundedRowsSemanticStatementChecks.actual_formula_substitution
      r.1 r.2 (foldFormula rs p) ν).trans (ih (Function.update ν r.1 r.2))

theorem foldSupport : FoldSupport := by
  intro reads p i
  induction reads with
  | nil => simp [foldFormula]
  | cons r rs ih =>
    change i ∈ (BoundedRows.substitute r.1 r.2 (foldFormula rs p)).variables ↔ _
    rw [BoundedRowsSemanticStatementChecks.exact_substitution_support,ih]
    simp only [List.map_cons,List.mem_cons,not_or]
    tauto

private theorem atomPlain (i n : Nat) (a : Atom)
    (h : ∀ s ∈ a.row.2, ∃ j : Nat, s.2 = .variable j) :
    ∀ s ∈ (BoundedRows.atomSubstitute i n a).row.2, ∃ j : Nat, s.2 = .variable j := by
  cases a with
  | nonnegative row =>
    intro s hs
    exact h s ((BoundedRowsSemanticProof.residual_mem i n row s).mp hs).1
  | divisible m row =>
    intro s hs
    exact h s ((BoundedRowsSemanticProof.residual_mem i n row s).mp hs).1

private theorem substitutePlain (i n : Nat) (p : Formula) :
    PlainPreparedFormula p → PlainPreparedFormula (BoundedRows.substitute i n p) := by
  induction p with
  | truth => intro h a ha; simp [BoundedRows.substitute,LinearRows.atoms] at ha
  | falsity => intro h a ha; simp [BoundedRows.substitute,LinearRows.atoms] at ha
  | atom a =>
    intro h b hb
    have hb' : b = BoundedRows.atomSubstitute i n a := List.mem_singleton.mp hb
    subst b
    exact atomPlain i n a (h a (by simp [LinearRows.atoms]))
  | negative p ih => exact ih
  | conjunction p q ihp ihq =>
    intro h a ha
    have hp : PlainPreparedFormula p := fun b hb => h b (List.mem_append_left _ hb)
    have hq : PlainPreparedFormula q := fun b hb => h b (List.mem_append_right _ hb)
    rcases List.mem_append.mp ha with hl | hr
    · exact ihp hp a hl
    · exact ihq hq a hr
  | disjunction p q ihp ihq =>
    intro h a ha
    have hp : PlainPreparedFormula p := fun b hb => h b (List.mem_append_left _ hb)
    have hq : PlainPreparedFormula q := fun b hb => h b (List.mem_append_right _ hb)
    rcases List.mem_append.mp ha with hl | hr
    · exact ihp hp a hl
    · exact ihq hq a hr

theorem foldPlain : FoldPlain := by
  intro reads p hp
  induction reads with
  | nil => exact hp
  | cons r rs ih => exact substitutePlain r.1 r.2 (foldFormula rs p) ih

theorem foldDualValuation : FoldDualValuation := by
  intro reads p ν μ hagree
  exact (foldActual reads p ν).trans
    (SourceTermGraphSupportProof.formula_eval_congr p (foldValuation reads ν) μ hagree)

theorem fullFold : FullFold :=
  ⟨foldCodeExact,foldActual,foldSupport,foldPlain,foldDualValuation⟩
end LogicLineages.PermittedControl.FiniteStripRecovery
