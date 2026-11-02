module
public import LogicLineages.OrdinalComparison.CommonHeadGuardReindexTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.CommonHeadGuardReindex.Proof
open CommonHeadLargeGuards

theorem exactRenaming : Targets.ExactRenaming := by
  intro σ p
  induction p with
  | truth => simp [rename,Formula.variables,Formula.eval]
  | falsity => simp [rename,Formula.variables,Formula.eval]
  | eq i j => simp [rename,Formula.variables,Formula.eval,Function.comp_def]
  | lt i j => simp [rename,Formula.variables,Formula.eval,Function.comp_def]
  | bound c i => simp [rename,Formula.variables,Formula.eval,Function.comp_def]
  | conj p q ihp ihq =>
    refine ⟨?_,?_⟩
    · simp only [rename,Formula.variables,List.map_append,ihp.1,ihq.1]
    · intro ν
      exact and_congr (ihp.2 ν) (ihq.2 ν)
  | disj p q ihp ihq =>
    refine ⟨?_,?_⟩
    · simp only [rename,Formula.variables,List.map_append,ihp.1,ihq.1]
    · intro ν
      exact or_congr (ihp.2 ν) (ihq.2 ν)
  | neg p ih =>
    exact ⟨ih.1,fun ν => not_congr (ih.2 ν)⟩

theorem equalConstant_eval (i c : Nat) (ν : Nat → Nat) :
    (equalConstant i c).eval ν ↔ ν i=c := by
  simp only [equalConstant,Formula.eval]
  omega

theorem guarded_eval (i c : Nat) (p : Formula) (ν : Nat → Nat) :
    (guarded i c p).eval ν ↔ ν i=c ∧ p.eval (ν ∘ skip i) := by
  exact and_congr (equalConstant_eval i c ν) ((exactRenaming (skip i) p).2 ν)
end LogicLineages.OrdinalComparison.CommonHeadGuardReindex.Proof
