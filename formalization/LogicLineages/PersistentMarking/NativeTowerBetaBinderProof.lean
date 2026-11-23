import LogicLineages.PersistentMarking.NativeTowerExtractorGeneralTargets
import LogicLineages.PersistentMarking.BoundBlockProof

namespace LogicLineages.PersistentMarking.NativeTowerBetaBinderProof
open Spine NativeTowerWitnessPrefixTargets NativeTowerExtractorGeneralTargets

theorem outerBinder (k : Nat) :
    ∀ (first : Nat) (q : Expr),
      bindAscending (k+1) first q = .lam (ty (first+k)) (bindAscending k first q) := by
  induction k with
  | zero => intros; rfl
  | succ k ih =>
    intro first q
    have edge := ih (first+1) (.lam (ty first) q)
    have index : (first+1)+k = first+(k+1) := by omega
    rw [index] at edge
    exact edge

theorem substituteUnderBinders (values : Args) (k : Nat) :
    ∀ (first : Nat) (q : Expr) (depth : Nat),
      substitute values depth (bindAscending k first q) =
        bindAscending k first (substitute values (depth+k) q) := by
  induction k with
  | zero => intros; rfl
  | succ k ih =>
    intro first q depth
    have edge := ih (first+1) (.lam (ty first) q) depth
    simpa only [bindAscending,substitute,Nat.add_assoc] using edge

/-- The literal head after some outer arguments were consumed. Values already
inserted are kept in nearest-binder order; k inner binders are still present. -/
def pending (k : Nat) (outer : Args) (body : Expr) : Expr :=
  bindAscending k 1 (substitute outer k body)

theorem pendingLambda (k : Nat) (outer : Args) (body : Expr) :
    pending (k+1) outer body =
      .lam (ty (k+1)) (bindAscending k 1 (substitute outer (k+1) body)) := by
  simpa only [pending,Nat.add_comm 1 k] using
    outerBinder k 1 (substitute outer (k+1) body)

theorem pendingBeta (k : Nat) (a : Expr) (outer : Args) (body : Expr) :
    substitute (.cons a .nil) 0 (bindAscending k 1 (substitute outer (k+1) body)) =
      pending k (.cons a outer) body := by
  rw [substituteUnderBinders,Nat.zero_add]
  exact congrArg (bindAscending k 1) (BoundBlockProof.block (.cons a .nil) outer k body)

#print axioms outerBinder
#print axioms substituteUnderBinders
#print axioms pendingLambda
#print axioms pendingBeta
end LogicLineages.PersistentMarking.NativeTowerBetaBinderProof
