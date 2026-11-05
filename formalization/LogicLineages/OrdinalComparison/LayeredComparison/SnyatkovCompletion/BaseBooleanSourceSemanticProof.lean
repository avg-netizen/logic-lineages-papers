module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BaseBooleanSourceTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BaseBooleanSourceProof
open BaseBooleanSource CommonLayerSyntax

theorem exactTranslation : BaseBooleanSourceTargets.ExactTranslation := by
  classical
  intro p ν
  induction p with
  | truth => simp [translate, SourceFormula.eval, BaseFormula.Formula.eval, BaseTerm.value]
  | falsity => simp [translate, SourceFormula.eval, BaseFormula.Formula.eval, BaseTerm.value]
  | equal a b => rfl
  | less a b => rfl
  | negative p ih => exact not_congr ih
  | conjunction p q ihp ihq => exact and_congr ihp ihq
  | disjunction p q ihp ihq =>
      change (¬(¬(translate p).eval ν ∧ ¬(translate q).eval ν)) ↔ (p.eval ν ∨ q.eval ν)
      rw [ihp, ihq]
      tauto

theorem exactSourceData : BaseBooleanSourceTargets.ExactSourceData := by
  intro p
  induction p <;> simp_all [translate, SourceBooleanGraph.test, SourceFormula.variables,
    BaseFormula.Formula.variables, BaseTerm.variables]

theorem exactPrefixTranslation : BaseBooleanSourceTargets.ExactPrefixTranslation := by
  classical
  intro xs p ν
  induction xs generalizing ν with
  | nil => exact ⟨exactTranslation p ν, exactTranslation p ν⟩
  | cons i xs ih =>
      constructor
      · change (∃ n : Nat, (SourceParameterDecision.existsBind xs (translate p)).eval (Function.update ν i n)) ↔
          ∃ n : Nat, existsPrefix (Function.update ν i n) xs p
        exact exists_congr (fun n => (ih (Function.update ν i n)).1)
      · change (¬∃ n : Nat, ¬(SourceParameterDecision.forallBind xs (translate p)).eval (Function.update ν i n)) ↔
          ∀ n : Nat, forallPrefix (Function.update ν i n) xs p
        simp only [not_exists, not_not]
        exact forall_congr' (fun n => (ih (Function.update ν i n)).2)

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BaseBooleanSourceProof
