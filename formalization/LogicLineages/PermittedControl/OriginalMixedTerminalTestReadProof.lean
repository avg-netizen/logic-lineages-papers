module
public import LogicLineages.PermittedControl.OriginalMixedTerminalTestTargets
import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BoundedSourceSemanticProof
import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceTermGraphSupportProof

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalMixedTerminalTest
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open SourceTermGraphSupportProof (source_value_congr formula_eval_congr)
open ArbitraryHeadSharedWire (Valuation)

private theorem rowTruth (θ : Valuation) (p : NormalForm.Formula) :
    rowAnswer θ p = true ↔ p.eval θ := by
  induction p with
  | truth => simp [rowAnswer,NormalForm.Formula.eval]
  | falsity => simp [rowAnswer,NormalForm.Formula.eval]
  | atom a =>
      cases a <;> simp [rowAnswer,NormalForm.Formula.eval,NormalForm.Atom.eval,
        Int.dvd_iff_emod_eq_zero]
  | negative q ih =>
      change (!rowAnswer θ q) = true ↔ ¬q.eval θ
      cases h : rowAnswer θ q <;> simp_all
  | conjunction a b iha ihb =>
      simp only [rowAnswer,NormalForm.Formula.eval,Bool.and_eq_true]
      exact and_congr iha ihb
  | disjunction a b iha ihb =>
      simp only [rowAnswer,NormalForm.Formula.eval,Bool.or_eq_true]
      exact or_congr iha ihb

private theorem answerTruth (p : Test) (hp : p.Admitted) (θ : Valuation) :
    p.answer θ = true ↔ p.eval θ := by
  cases p with
  | rows q => exact rowTruth θ q
  | bounded q => exact BoundedSourceProof.actualTruth q hp θ

theorem exactTerminalTestRead : ExactTerminalTestRead := by
  intro p hp θ positive
  have h := answerTruth p hp θ
  cases positive with
  | true => exact h
  | false =>
      change p.answer θ = false ↔ ¬ p.eval θ
      cases hb : p.answer θ with
      | false =>
          rw [hb] at h
          constructor
          · intro _ eval
            have bad := h.mpr eval
            cases bad
          · intro _
            rfl
      | true =>
          rw [hb] at h
          constructor
          · intro eq
            cases eq
          · intro no
            exact (no (h.mp rfl)).elim

private theorem sourceStable (p : SourceFormula) (ν θ : Valuation)
    (same : ∀ n ∈ p.variables, θ n = ν n) : p.eval θ ↔ p.eval ν := by
  induction p generalizing ν θ with
  | equal a b =>
      change a.value θ = b.value θ ↔ a.value ν = b.value ν
      rw [source_value_congr a θ ν (fun n hn => same n (List.mem_append_left _ hn)),
        source_value_congr b θ ν (fun n hn => same n (List.mem_append_right _ hn))]
  | less a b =>
      change a.value θ < b.value θ ↔ a.value ν < b.value ν
      rw [source_value_congr a θ ν (fun n hn => same n (List.mem_append_left _ hn)),
        source_value_congr b θ ν (fun n hn => same n (List.mem_append_right _ hn))]
  | negative q ih => exact not_congr (ih ν θ same)
  | conjunction a b iha ihb =>
      exact and_congr (iha ν θ (fun n hn => same n (List.mem_append_left _ hn)))
        (ihb ν θ (fun n hn => same n (List.mem_append_right _ hn)))
  | existsNat i q ih =>
      change (∃ n : Nat, q.eval (Function.update θ i n)) ↔
        ∃ n : Nat, q.eval (Function.update ν i n)
      have atValue (a : Nat) : q.eval (Function.update θ i a) ↔ q.eval (Function.update ν i a) := by
        apply ih
        intro n hn
        by_cases eq : n = i
        · subst n
          simp only [Function.update_self]
        · simp only [Function.update_of_ne eq]
          exact same n (List.mem_filter.mpr ⟨hn,by simp [eq]⟩)
      exact exists_congr atValue

private theorem freeListed (p : SourceFormula) (n : Nat) (h : n ∈ p.variables) :
    n ∈ boundedNames p := by
  induction p with
  | equal a b => exact h
  | less a b => exact h
  | negative q ih => exact ih h
  | conjunction a b iha ihb =>
      rcases List.mem_append.mp h with ha | hb
      · exact List.mem_append_left _ (iha ha)
      · exact List.mem_append_right _ (ihb hb)
  | existsNat i q ih =>
      exact List.mem_cons_of_mem _ (ih (List.mem_filter.mp h).1)

theorem literalTestStable (p : Test) (ν θ : Valuation)
    (same : ∀ n ∈ p.names, θ n = ν n) : p.eval θ ↔ p.eval ν := by
  cases p with
  | rows q => exact formula_eval_congr q θ ν same
  | bounded q => exact sourceStable q ν θ (fun n hn => same n (freeListed q n hn))

end LogicLineages.PermittedControl.OriginalMixedTerminalTest
