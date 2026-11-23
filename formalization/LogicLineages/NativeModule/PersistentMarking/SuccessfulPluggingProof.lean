module

public import LogicLineages.NativeModule.PersistentMarking.ApplicationCovarianceTargets
public import LogicLineages.NativeModule.PersistentMarking.BoundBlockProof

@[expose] public section

namespace LogicLineages.PersistentMarking.SuccessfulPluggingProof
open Spine

theorem plugging (q : Expr) (newer older args : Args) (w : Expr)
    (hc : applyAux q args (newer.append older) = some w) :
    applyAux (substitute older newer.length q) args newer = some w := by
  cases args with
  | nil =>
    have hb := BoundBlockProof.block newer older 0 q
    simp only [Nat.zero_add] at hb
    simpa only [applyAux,hb] using hc
  | cons a rest =>
    cases q with
    | free σ x => simp [applyAux] at hc
    | bound σ i => simp [applyAux] at hc
    | lam σ body =>
      by_cases ht : a.type = σ
      · have hi : applyAux body rest ((Args.cons a newer).append older) = some w := by
          simpa only [applyAux,ht,if_true,Args.append] using hc
        have hh := plugging body (.cons a newer) older rest w hi
        simpa only [substitute,applyAux,ht,if_true,Args.length,Nat.add_comm] using hh
      · simp [applyAux,ht] at hc
    | head f base =>
      have hb := BoundBlockProof.blockArgs newer older 0 base
      simp only [Nat.zero_add] at hb
      simpa only [substitute,applyAux,hb] using hc
    | marked f τ base extras =>
      have hb := BoundBlockProof.blockArgs newer older 0 base
      have he := BoundBlockProof.blockArgs newer older 0 extras
      simp only [Nat.zero_add] at hb he
      simpa only [substitute,applyAux,hb,he] using hc
termination_by sizeOf args

theorem successfulAuxPlugging : ApplicationCovarianceTargets.SuccessfulAuxPlugging := plugging

theorem auxNilValues {q : Expr} {args : Args} {r : Expr} (h : applyAux q args .nil = some r) : apply q args = some r := by
  cases args with
  | nil => simpa only [apply,applyAux,SubstitutionProof.emptySubstitution] using h
  | cons a rest => exact h
end LogicLineages.PersistentMarking.SuccessfulPluggingProof
