module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceParameterDecisionTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainParameterDecisionCorrectnessProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceBooleanGraphDecisionProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceParameterDecisionProof
open CommonLayerSyntax SourceParameterDecision

theorem actualBlockTranslation : SourceParameterDecisionTargets.ActualBlockTranslation := by
  intro xs p ν hp
  induction xs generalizing ν with
  | nil => exact SourceBooleanGraphProof.actualExistentialMatrix p ν hp
  | cons i xs ih =>
      change (∃ n : Nat, NormalForm.existsPrefix (Function.update ν i n)
        (xs ++ witnesses p) (SourceBooleanGraph.compile p)) ↔
          ∃ n : Nat, (existsBind xs p).eval (Function.update ν i n)
      exact exists_congr (fun n => ih (Function.update ν i n))

theorem forallBind_not_exists (xs : List Nat) (p : SourceFormula) (ν : Nat → Nat) :
    (forallBind xs p).eval ν ↔ ¬(existsBind xs (.negative p)).eval ν := by
  classical
  induction xs generalizing ν with
  | nil => simp only [forallBind, existsBind, List.foldr_nil, SourceFormula.eval, not_not]
  | cons i xs ih =>
      change (¬∃ n : Nat, ¬(forallBind xs p).eval (Function.update ν i n)) ↔
        ¬∃ n : Nat, (existsBind xs (.negative p)).eval (Function.update ν i n)
      simp only [not_exists, not_not]
      exact forall_congr' (fun n => ih (Function.update ν i n))

theorem exists_domain (xs values : List Nat) (p : SourceFormula) :
    (decideExists xs values p).isSome = SourceBooleanGraph.test p := by
  by_cases hp : SourceBooleanGraph.test p = true
  · rw [decideExists, if_pos hp, hp]
    exact (PlainParameterDecisionProof.exactDecisionDomains (xs ++ witnesses p) values
      (SourceBooleanGraph.compile p)).1.trans
        (SourceBooleanGraphProof.plainCompiledMatrix p (SourceBooleanGraph.start p))
  · simp [decideExists, hp, Bool.eq_false_iff.mpr hp]

theorem exactDecisionDomain : SourceParameterDecisionTargets.ExactDecisionDomain := by
  intro xs values p
  refine ⟨exists_domain xs values p, ?_⟩
  simpa only [decideForall, Option.isSome_map, SourceBooleanGraph.test] using
    exists_domain xs values (.negative p)

theorem exists_correct (xs values : List Nat) (p : SourceFormula)
    (hp : SourceBooleanGraph.test p = true) (b : Bool) :
    decideExists xs values p = some b ↔
      ((existsBind xs p).eval (PlainParameterDecision.valuation values) ↔ b = true) := by
  rw [decideExists, if_pos hp,
    PlainParameterDecisionProof.existsDecision_correct (xs ++ witnesses p) values
      (SourceBooleanGraph.compile p)
      (SourceBooleanGraphProof.plainCompiledMatrix p (SourceBooleanGraph.start p)) b,
    actualBlockTranslation xs p (PlainParameterDecision.valuation values) hp]

private theorem option_not (x : Option Bool) (b : Bool) :
    x.map Bool.not = some b ↔ x = some (!b) := by
  cases x with
  | none => simp
  | some c => cases c <;> cases b <;> simp

theorem forall_correct (xs values : List Nat) (p : SourceFormula)
    (hp : SourceBooleanGraph.test p = true) (b : Bool) :
    decideForall xs values p = some b ↔
      ((forallBind xs p).eval (PlainParameterDecision.valuation values) ↔ b = true) := by
  classical
  have hn : SourceBooleanGraph.test (.negative p) = true := hp
  rw [decideForall, option_not, exists_correct xs values (.negative p) hn (!b), forallBind_not_exists]
  cases b <;> simp

theorem actualSourceDecisions : SourceParameterDecisionTargets.ActualSourceDecisions :=
  fun xs values p hp b => ⟨exists_correct xs values p hp b, forall_correct xs values p hp b⟩

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceParameterDecisionProof
