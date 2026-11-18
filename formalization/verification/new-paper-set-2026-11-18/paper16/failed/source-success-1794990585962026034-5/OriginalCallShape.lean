import LogicLineages.PersistentMarking.ApplicationCovarianceTargets
import LogicLineages.PersistentMarking.ElementarySupportProof
import LogicLineages.PersistentMarking.SpineCallTypingProof
namespace LogicLineages.PersistentMarking.OriginalCallShape
open Spine NameBridge ElementarySupportProof

/-- Exact original-variable blocking, independently of substituted values.
Typing supplies the separate argument/domain checks. -/
def Blocked : Expr → Nat → Prop
  | _, 0 => False
  | .lam _ body, n+1 => Blocked body n
  | .free _ _, _+1 => True
  | .bound _ _, _+1 => True
  | .head _ _, _+1 => False
  | .marked _ _ _ _, _+1 => False

theorem opening (σ : Ty) (x d : Nat) (q : Expr) (n : Nat) :
    Blocked (substitute (.cons (.free σ x) .nil) d q) n ↔ Blocked q n := by
  cases q with
  | free τ y => rfl
  | bound τ i =>
    by_cases hi : i < d
    · simp [substitute,hi]
    · cases hn : i-d with
      | zero => cases n <;> simp [substitute,hi,hn,Args.get,shift,Blocked]
      | succ j => cases n <;> simp [substitute,hi,hn,Args.get,Blocked]
  | lam τ q =>
    cases n with
    | zero => exact Iff.rfl
    | succ n => exact opening σ x (d+1) q n
  | head f base => cases n <;> exact Iff.rfl
  | marked f τ base extras => cases n <;> exact Iff.rfl
termination_by sizeOf q

theorem auxSuccess (q : Expr) (args values : Args) (τ : Ty)
    (ht : CallTyped EmptyContext q.type args τ) :
    (∃ r, applyAux q args values = some r) ↔ ¬ Blocked q args.length := by
  cases args with
  | nil => simp [applyAux,Args.length,Blocked]
  | cons a rest =>
    cases q with
    | free σ x => simp [applyAux,Args.length,Blocked]
    | bound σ i => simp [applyAux,Args.length,Blocked]
    | lam σ body =>
      cases ht with
      | cons ha hr =>
        have hat := SpineShiftProof.annotationExact _ _ _ ha
        have hi := auxSuccess body rest (.cons a values) τ hr
        simpa only [applyAux,hat,if_true,Args.length,Nat.add_comm,Blocked] using hi
    | head f base =>
      have hc := SpineCallTypingProof.consumeExact _ _ _ _ ht
      simp only [Expr.type] at hc
      simp [applyAux,hc,Args.length,Blocked]
    | marked f σ base extras =>
      have hc := SpineCallTypingProof.consumeExact _ _ _ _ ht
      simp only [Expr.type] at hc
      simp [applyAux,hc,Args.length,Blocked]
termination_by sizeOf args

theorem fullSuccess (q : Expr) (args : Args) (τ : Ty) (ht : CallTyped EmptyContext q.type args τ) :
    (∃ r, apply q args = some r) ↔ ¬ Blocked q args.length := by
  cases args with
  | nil => simp [apply,Args.length,Blocked]
  | cons a rest => exact auxSuccess q (.cons a rest) .nil τ ht
end LogicLineages.PersistentMarking.OriginalCallShape
