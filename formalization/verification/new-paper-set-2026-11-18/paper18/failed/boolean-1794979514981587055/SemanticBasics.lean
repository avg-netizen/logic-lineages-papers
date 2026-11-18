module
public import LogicLineages.StandardControlCurrent.PolynomialBoolean.Targets
public import LogicLineages.OrdinalComparison.PolynomialGraphCompletion.ExpressionSemanticStatementChecks
public import LogicLineages.OrdinalComparison.PolynomialGraphCompletion.ExpressionSupportProof

@[expose] public section
namespace LogicLineages.StandardControlCurrent.PolynomialBoolean.SemanticBasics
open OrdinalComparison PolynomialGraphCompletion
open ExpressionSupportProof

 theorem end_ge (start : Nat) (p : Source) : start ≤ (compile start p).1 := by
  induction p generalizing start with
  | truth b => exact le_rfl
  | atom r a b => simp only [compile]; omega
  | neg p ih => exact ih start
  | conj p q ihp ihq | disj p q ihp ihq =>
    exact (ihp start).trans (ihq (compile start p).1)

 theorem row_negative (r : Row) (ν : Nat → Nat) :
    RowValue (negativeRow r) ν = -RowValue r ν := by
  rcases r with ⟨c,rs⟩
  simp only [RowValue, negativeRow, List.map_map, Function.comp_apply]
  have h : (rs.map (fun a => -a.1 * (wordValue a.2.2 (ν a.2.1) : Int))).sum =
      -(rs.map (fun a => a.1 * (wordValue a.2.2 (ν a.2.1) : Int))).sum := by
    induction rs with
    | nil => simp
    | cons a rs ih => simp only [List.map_cons,List.sum_cons]; rw [ih]; ring
  change -c + (rs.map (fun a => -a.1 * (wordValue a.2.2 (ν a.2.1) : Int))).sum = _
  rw [h]
  omega

 theorem equality_eval (r : Row) (ν : Nat → Nat) :
    WordLinearDecisionCompletion.Formula.eval ν (equality r) ↔ RowValue r ν = 0 := by
  simp only [equality,WordLinearDecisionCompletion.Formula.eval,
    WordLinearDecisionCompletion.Atom.eval,row_negative]
  omega

 theorem output_eval (r : Relation) (a b : Nat) (ν : Nat → Nat) :
    WordLinearDecisionCompletion.Formula.eval ν (outputTest r a b) ↔
      (match r with
      | .equal => ν a = ν b
      | .weak => ν a ≤ ν b
      | .strict => ν a < ν b) := by
  cases r <;> simp [outputTest,equality_eval,WordLinearDecisionCompletion.Formula.eval,
    WordLinearDecisionCompletion.Atom.eval,RowValue,relationRow,wordValue] <;> omega

 theorem graph_eval (rs : List Row) (ν : Nat → Nat) :
    WordLinearDecisionCompletion.Formula.eval ν (graphFormula rs) ↔
      ∀ r ∈ rs, RowValue r ν = 0 := by
  induction rs with
  | nil => simp [graphFormula,WordLinearDecisionCompletion.Formula.eval]
  | cons r rs ih =>
    simp only [graphFormula,List.foldr_cons,WordLinearDecisionCompletion.Formula.eval,equality_eval]
    change (RowValue r ν = 0 ∧ WordLinearDecisionCompletion.Formula.eval ν (graphFormula rs)) ↔ _
    simp only [ih,List.mem_cons,forall_eq_or_imp]

 theorem positive_eval (d : Nat) (ν : Nat → Nat) :
    WordLinearDecisionCompletion.Formula.eval ν (positiveFormula d) ↔ Positive d ν := by
  have aux : ∀ is : List Nat,
      WordLinearDecisionCompletion.Formula.eval ν
        (is.foldr (fun i q => .conj (.atom (.nonnegative (-1,[(1,i,[])]))) q) .top) ↔
      ∀ i ∈ is, 0 < ν i := by
    intro is
    induction is with
    | nil => simp [WordLinearDecisionCompletion.Formula.eval]
    | cons i is ih =>
      simp only [List.foldr_cons,WordLinearDecisionCompletion.Formula.eval,
        WordLinearDecisionCompletion.Atom.eval,RowValue,List.map_cons,List.map_nil,
        List.sum_cons,List.sum_nil,wordValue,one_mul,add_zero]
      rw [ih]
      simp only [List.mem_cons,forall_eq_or_imp]
      omega
  simpa only [positiveFormula,Positive,List.mem_range] using aux (List.range d)

 theorem source_congr (d : Nat) (p : Source) (h : p.Valid d) (ν μ : Nat → Nat)
    (hf : ∀ i, i < d → ν i = μ i) : p.eval ν ↔ p.eval μ := by
  induction p with
  | truth b => cases b <;> rfl
  | atom r a b =>
    have ha := source_value_congr a ν μ (fun i hi => hf i (h.2.2.1 i hi))
    have hb := source_value_congr b ν μ (fun i hi => hf i (h.2.2.2 i hi))
    cases r <;> simp only [Source.eval,ha,hb]
  | neg p ih => exact not_congr (ih h)
  | conj p q ihp ihq => exact and_congr (ihp h.1) (ihq h.2)
  | disj p q ihp ihq => exact or_congr (ihp h.1) (ihq h.2)

 theorem expression_rows_below (d start : Nat) (t : Expr)
    (hs : d ≤ start) (hv : ∀ i ∈ t.variables, i < d)
    (r : Row) (hr : r ∈ rows start t) (i : Nat) (hi : i ∈ rowVariables r) :
    i < start + nodeCount t := by
  rcases rows_support start t r hr i hi with h | h
  · exact (hv i h).trans_le (hs.trans (Nat.le_add_right _ _))
  · exact ((mem_allocated start t i).mp h).2

 theorem rows_below (d start : Nat) (p : Source) (hv : p.Valid d) (hs : d ≤ start)
    (r : Row) (hr : r ∈ (compile start p).2.1) (i : Nat) (hi : i ∈ rowVariables r) :
    i < (compile start p).1 := by
  induction p generalizing start with
  | truth b => simp [compile] at hr
  | atom rel a b =>
    rcases List.mem_append.mp hr with ha | hb
    · exact (expression_rows_below d start a hs hv.2.2.1 r ha i hi).trans_le (Nat.le_add_right _ _)
    · exact expression_rows_below d (start+nodeCount a) b (by omega) hv.2.2.2 r hb i hi
  | neg p ih => exact ih start hv hs hr
  | conj p q ihp ihq | disj p q ihp ihq =>
    rcases List.mem_append.mp hr with hp | hq
    · exact (ihp start hv.1 hs hp).trans_le (end_ge (compile start p).1 q)
    · exact ihq (compile start p).1 hv.2 (hs.trans (end_ge start p)) hq

 theorem graph_frame (d start : Nat) (p : Source) (hv : p.Valid d) (hs : d ≤ start)
    (ν μ : Nat → Nat) (hf : ∀ i, i < (compile start p).1 → ν i = μ i) :
    RowsHold (compile start p).2.1 ν ↔ RowsHold (compile start p).2.1 μ :=
  rows_hold_congr _ ν μ (fun r hr i hi => hf i (rows_below d start p hv hs r hr i hi))

 theorem output_frame (start : Nat) (p : Source) (ν μ : Nat → Nat)
    (hf : ∀ i, i < (compile start p).1 → ν i = μ i) :
    WordLinearDecisionCompletion.Formula.eval ν (compile start p).2.2 ↔
    WordLinearDecisionCompletion.Formula.eval μ (compile start p).2.2 := by
  induction p generalizing start with
  | truth b => cases b <;> rfl
  | atom r a b =>
    have ha := (mem_allocated start a (output start a)).mp (output_mem_allocated start a)
    have hb := (mem_allocated (start+nodeCount a) b (output (start+nodeCount a) b)).mp
      (output_mem_allocated (start+nodeCount a) b)
    simp only [compile,output_eval]
    have hA := hf (output start a) (by simpa only [compile] using ha.2.trans_le (Nat.le_add_right _ (nodeCount b)))
    have hB := hf (output (start+nodeCount a) b) hb.2
    cases r <;> simp only [hA,hB]
  | neg p ih => exact not_congr (ih start hf)
  | conj p q ihp ihq =>
    exact and_congr (ihp start (fun i hi => hf i (hi.trans_le (end_ge (compile start p).1 q))))
      (ihq (compile start p).1 hf)
  | disj p q ihp ihq =>
    exact or_congr (ihp start (fun i hi => hf i (hi.trans_le (end_ge (compile start p).1 q))))
      (ihq (compile start p).1 hf)

 theorem globalSoundness : Targets.GlobalSoundness := by
  intro d start p hv hs ν hrows
  induction p generalizing start with
  | truth b => cases b <;> simp [compile,Source.eval,WordLinearDecisionCompletion.Formula.eval]
  | atom r a b =>
    have ha := ExpressionSemanticStatementChecks.graph_soundness start a hv.1 ν
      (fun row hr => hrows row (List.mem_append_left _ hr))
    have hb := ExpressionSemanticStatementChecks.graph_soundness (start+nodeCount a) b hv.2.1 ν
      (fun row hr => hrows row (List.mem_append_right _ hr))
    simp only [compile,output_eval,ha,hb]
    cases r <;> rfl
  | neg p ih => exact not_congr (ih start hv hs hrows)
  | conj p q ihp ihq =>
    exact and_congr (ihp start hv.1 hs (fun row hr => hrows row (List.mem_append_left _ hr)))
      (ihq (compile start p).1 hv.2 (hs.trans (end_ge start p)) (fun row hr => hrows row (List.mem_append_right _ hr)))
  | disj p q ihp ihq =>
    exact or_congr (ihp start hv.1 hs (fun row hr => hrows row (List.mem_append_left _ hr)))
      (ihq (compile start p).1 hv.2 (hs.trans (end_ge start p)) (fun row hr => hrows row (List.mem_append_right _ hr)))

end LogicLineages.StandardControlCurrent.PolynomialBoolean.SemanticBasics
