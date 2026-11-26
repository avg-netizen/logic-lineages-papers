module
public import LogicLineages.StandardControlCurrent.RankedRowTargets
public import LogicLineages.StandardControlCurrent.OrderedGuardsCalibrationProof
public import LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.RunnerStatementChecks
@[expose] public section
namespace LogicLineages.StandardControlCurrent.RankedRowProof
open OrdinalComparison PolynomialGraphCompletion RankedWordDecisionCompletion

theorem rowCalibration : RankedRowTargets.RowCalibration := by
  intro D r hr ν
  have hdom : RankedRow.RowDomain r ν ↔ RowDomain r ν := by
    constructor
    · intro h a ha
      exact (OrderedGuardsProof.wordCalibration D _ (hr a ha) _).1.mp (h a ha)
    · intro h a ha
      exact (OrderedGuardsProof.wordCalibration D _ (hr a ha) _).1.mpr (h a ha)
  refine ⟨hdom,?_⟩
  intro h
  unfold RankedRow.RowValue RowValue
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro a ha
  rw [(OrderedGuardsProof.wordCalibration D _ (hr a ha) _).2 (h a ha)]

theorem packageCalibration (D maximum : Nat) (rows : List Row) (p : Package)
    (hr : ∀ r ∈ rows, RowAllowed D r) (hp : PackageCorrect D maximum rows p) :
    RankedRow.PackageCorrect D maximum rows p := by
  refine ⟨hp.1,?_⟩
  intro ν hregion
  have h := hp.2 ν hregion
  have hd : ∀ r ∈ rows, RankedRow.RowDomain r ν :=
    fun r hmem => (rowCalibration D r (hr r hmem) ν).1.mpr (h.1 r hmem)
  have hod : ∀ c ∈ p.cases, ∀ o ∈ c.outcomes, RankedRow.RowDomain o.row ν := by
    intro c hc o ho
    exact (rowCalibration D o.row ((hp.1 c hc).2.2.2.2 o ho).1 ν).1.mpr
      ((h.2.1 c hc).2 o ho)
  refine ⟨hd,fun c hc => ⟨(h.2.1 c hc).1,hod c hc⟩,h.2.2.1,?_⟩
  intro c hc hguard
  have hrel := h.2.2.2 c hc hguard
  have hsource : ∀ r ∈ rows, RankedRow.RowValue r ν = RowValue r ν :=
    fun r hm => (rowCalibration D r (hr r hm) ν).2 (hd r hm)
  have hout : ∀ o ∈ c.outcomes, RankedRow.RowValue o.row ν = RowValue o.row ν :=
    fun o hm => (rowCalibration D o.row ((hp.1 c hc).2.2.2.2 o hm).1 ν).2 (hod c hc o hm)
  have transport : ∀ rs os, List.Forall₂ (fun r o => OutcomeCorrect maximum r o ν) rs os →
      (∀ r ∈ rs, RankedRow.RowValue r ν = RowValue r ν) →
      (∀ o ∈ os, RankedRow.RowValue o.row ν = RowValue o.row ν) →
      List.Forall₂ (fun r o => RankedRow.OutcomeCorrect maximum r o ν) rs os := by
    intro rs os hro
    induction hro with
    | nil => intro _ _; exact .nil
    | @cons r o rs os hhead htail ih =>
      intro hrv hov
      refine .cons ?_ (ih (fun r hm => hrv r (by simp [hm])) (fun o hm => hov o (by simp [hm])))
      simpa only [RankedRow.OutcomeCorrect,OutcomeCorrect,hrv r (by simp),hov o (by simp)] using hhead
  exact transport rows c.outcomes hrel hsource hout

theorem full : RankedRowTargets.Full := by
  refine ⟨rowCalibration,StatementChecks.all_input_termination,StatementChecks.exact_least_stopping,
    StatementChecks.finite_runner_program,StatementChecks.least_fuel_program,?_,?_,StatementChecks.actual_family_program⟩
  · intro D maximum r hD hr
    exact packageCalibration D maximum [r] _ (by intro s hs; have he := List.mem_singleton.mp hs; subst s; exact hr)
      (StatementChecks.exact_single_row_package D maximum r hD hr)
  · intro D maximum rows hD hr
    exact packageCalibration D maximum rows _ hr (StatementChecks.exact_family_package D maximum rows hD hr)
end LogicLineages.StandardControlCurrent.RankedRowProof
