module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.AdditiveSourceTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ClosedLinearSemanticProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceRowsSemanticProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.AdditiveSourceProof
open CommonLayerSyntax NormalForm SourceTermGraph SourceRows AdditiveSource

theorem purelyLinearGeneratedRows : AdditiveSourceTargets.PurelyLinearGeneratedRows := by
  intro t
  induction t with
  | numeral n =>
      intro _ start row hr
      simp only [rows, List.mem_singleton] at hr
      subst row
      simp [numeralRow]
  | «variable» i =>
      intro _ start row hr
      simp only [rows, List.mem_singleton] at hr
      subst row
      simp [variableRow]
  | add a b iha ihb =>
      intro h start row hr
      have hh := Bool.and_eq_true_iff.mp h
      simp only [rows, List.mem_append, List.mem_singleton] at hr
      rcases hr with (ha | hb) | hr
      · exact iha hh.1 start row ha
      · exact ihb hh.2 (start + nodeCount a) row hb
      · subst row
        simp [additionRow]
  | phi a ih =>
      intro h
      simp [termTest] at h

private theorem pureRow_linear (i : Nat) (row : Row)
    (h : ∀ a ∈ row.2, ∃ j : Nat, a.2 = Summand.variable j) :
    LinearRows.rowLinear i row = true := by
  apply List.all_eq_true.mpr
  intro a ha
  obtain ⟨j, hj⟩ := h a ha
  simp only [hj, LinearRows.summandLinear]

private theorem equation_linear (i : Nat) (row : Row) :
    LinearRows.isLinear i (equation row) = LinearRows.rowLinear i row := by
  simp [LinearRows.isLinear, LinearRows.atoms, equation, Atom.row,
    LinearRows.rowLinear, negateRow, List.all_map]

private theorem equations_linear (i : Nat) (rs : List Row)
    (h : ∀ row ∈ rs, LinearRows.rowLinear i row = true) :
    LinearRows.isLinear i (equations rs) = true := by
  induction rs with
  | nil => rfl
  | cons row rs ih =>
      have hr := h row (List.mem_cons_self ..)
      have hs := ih (fun r hm => h r (List.mem_cons_of_mem _ hm))
      have he := equation_linear i row
      simpa only [equations, List.foldr_cons, LinearRows.isLinear, LinearRows.atoms,
        List.all_append] using Bool.and_eq_true_iff.mpr ⟨he.trans hr, hs⟩

private theorem graph_linear (i start : Nat) (t : BaseTerm) (h : termTest t = true) :
    LinearRows.isLinear i (graph start t) = true :=
  equations_linear i (rows start t) (fun row hr =>
    pureRow_linear i row (purelyLinearGeneratedRows t h start row hr))

private theorem relation_linear (i : Nat) (strict : Bool) (x y : Nat) :
    LinearRows.isLinear i (relation strict x y) = true := by
  cases strict <;> simp [relation, strictRow, equation, negateRow, variableRow,
    LinearRows.isLinear, LinearRows.atoms, Atom.row, LinearRows.rowLinear,
    LinearRows.summandLinear]

private theorem atomBody_linear (i : Nat) (strict : Bool) (a b : BaseTerm)
    (ha : termTest a = true) (hb : termTest b = true) :
    LinearRows.isLinear i (atomBody strict a b) = true := by
  have hg := graph_linear i (localStart a b) (.add a b) (by simp [termTest, ha, hb])
  have hr := relation_linear i strict (output (localStart a b) a)
    (output (localStart a b + nodeCount a) b)
  simpa only [atomBody, LinearRows.isLinear, LinearRows.atoms, List.all_append] using
    Bool.and_eq_true_iff.mpr ⟨hg, hr⟩

private theorem localAtom_linear (strict : Bool) (a b : BaseTerm)
    (ha : termTest a = true) (hb : termTest b = true) :
    QuantifiedLinear.admissible (localAtom strict a b) = true ∧
      ∀ i, QuantifiedLinear.freeLinear i (localAtom strict a b) = true := by
  constructor
  · rw [localAtom, QuantifiedLinearProof.admissible_bindAll]
    apply (LinearBlockProof.exactBlockTest _ _).mpr
    intro i _
    exact atomBody_linear i strict a b ha hb
  · intro i
    rw [localAtom, QuantifiedLinearProof.freeLinear_bindAll]
    split
    · rfl
    · exact atomBody_linear i strict a b ha hb

private theorem source_linear (p : SourceFormula) (h : test p = true) :
    QuantifiedLinear.admissible (SourceRows.translate p) = true ∧
      ∀ i, QuantifiedLinear.freeLinear i (SourceRows.translate p) = true := by
  induction p with
  | equal a b =>
      have hh := Bool.and_eq_true_iff.mp h
      exact localAtom_linear false a b hh.1 hh.2
  | less a b =>
      have hh := Bool.and_eq_true_iff.mp h
      exact localAtom_linear true a b hh.1 hh.2
  | negative p ih => exact ih h
  | conjunction p q ihp ihq =>
      have hh := Bool.and_eq_true_iff.mp h
      have hp := ihp hh.1
      have hq := ihq hh.2
      constructor
      · exact Bool.and_eq_true_iff.mpr ⟨hp.1, hq.1⟩
      · intro i
        exact Bool.and_eq_true_iff.mpr ⟨hp.2 i, hq.2 i⟩
  | existsNat j p ih =>
      have hp := ih h
      constructor
      · exact Bool.and_eq_true_iff.mpr ⟨hp.1, hp.2 j⟩
      · intro i
        change (if i = j then true else _) = true
        split
        · rfl
        · exact hp.2 i

theorem actualAdmissibility : AdditiveSourceTargets.ActualAdmissibility :=
  fun p h => (source_linear p h).1

theorem actualQuantifierElimination : AdditiveSourceTargets.ActualQuantifierElimination := by
  intro p h ν
  exact (QuantifiedLinearProof.actualQuantifierElimination (SourceRows.translate p)
    (actualAdmissibility p h) ν).trans (SourceRowsSemanticProof.exactSourceIntroduction p ν)

theorem exactOutputSupport : AdditiveSourceTargets.ExactOutputSupport := by
  intro p i
  exact (QuantifiedLinearProof.exactFreeVariableSupport (SourceRows.translate p) i).trans
    (SourceRowsSupportProof.exactFreeVariableMembership p i)

private theorem translated_closed (p : SourceFormula) :
    (SourceRows.translate p).variables.isEmpty = p.variables.isEmpty := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.isEmpty_iff]
  constructor
  · intro h
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro i hi
    have he := (SourceRowsSupportProof.exactFreeVariableMembership p i).mpr hi
    simpa [h] using he
  · intro h
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro i hi
    have he := (SourceRowsSupportProof.exactFreeVariableMembership p i).mp hi
    simpa [h] using he

theorem exactDecisionDomain : AdditiveSourceTargets.ExactDecisionDomain := by
  intro p
  by_cases h : test p = true
  · rw [decideClosed, if_pos h, ClosedLinearProof.exactDecisionDomain,
      actualAdmissibility p h, translated_closed, h]
  · simp [decideClosed, h]

theorem actualClosedDecision : AdditiveSourceTargets.ActualClosedDecision := by
  intro p h hclosed ν answer
  have hc : (SourceRows.translate p).variables = [] := by
    apply List.isEmpty_iff.mp
    rw [translated_closed, hclosed]
    rfl
  rw [decideClosed, if_pos h,
    ClosedLinearProof.actualClosedDecision (SourceRows.translate p)
      (actualAdmissibility p h) hc ν answer,
    SourceRowsSemanticProof.exactSourceIntroduction p ν]

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.AdditiveSourceProof
