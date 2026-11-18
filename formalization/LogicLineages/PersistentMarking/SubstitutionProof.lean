import LogicLineages.PersistentMarking.SubstitutionTargets
namespace LogicLineages.PersistentMarking.SubstitutionProof
open Spine

mutual
 theorem shiftZero (t : Expr) (cutoff : Nat) : shift 0 cutoff t = t := by
  cases t with
  | free σ x => rfl
  | bound σ i => simp [shift]
  | lam σ body => simp only [shift, shiftZero body]
  | head f base => simp only [shift, shiftArgsZero base]
  | marked f τ base extras => simp only [shift, shiftArgsZero base, shiftArgsZero extras]
 termination_by sizeOf t
 theorem shiftArgsZero (ts : Args) (cutoff : Nat) : shiftArgs 0 cutoff ts = ts := by
  cases ts with
  | nil => rfl
  | cons x xs => simp only [shiftArgs, shiftZero x, shiftArgsZero xs]
 termination_by sizeOf ts
end

mutual
 theorem shiftAdd (t : Expr) (a b cutoff : Nat) :
    shift a cutoff (shift b cutoff t) = shift (b+a) cutoff t := by
  cases t with
  | free σ x => rfl
  | bound σ i =>
    by_cases hi : i < cutoff
    · simp [shift, hi]
    · have hj : ¬ i+b < cutoff :=
        Nat.not_lt_of_ge (Nat.le_trans (Nat.le_of_not_lt hi) (Nat.le_add_right i b))
      simp [shift, hi, hj, Nat.add_assoc]
  | lam σ body => simp only [shift, shiftAdd body]
  | head f base => simp only [shift, shiftArgsAdd base]
  | marked f τ base extras => simp only [shift, shiftArgsAdd base, shiftArgsAdd extras]
 termination_by sizeOf t
 theorem shiftArgsAdd (ts : Args) (a b cutoff : Nat) :
    shiftArgs a cutoff (shiftArgs b cutoff ts) = shiftArgs (b+a) cutoff ts := by
  cases ts with
  | nil => rfl
  | cons x xs => simp only [shiftArgs, shiftAdd x, shiftArgsAdd xs]
 termination_by sizeOf ts
end

mutual
 theorem emptySubstitution (t : Expr) (depth : Nat) : substitute .nil depth t = t := by
  cases t with
  | free σ x => rfl
  | bound σ i => simp [substitute, Args.get, Args.length]
  | lam σ body => simp only [substitute, emptySubstitution body]
  | head f base => simp only [substitute, emptyArgsSubstitution base]
  | marked f τ base extras =>
    simp only [substitute, emptyArgsSubstitution base, emptyArgsSubstitution extras]
 termination_by sizeOf t
 theorem emptyArgsSubstitution (ts : Args) (depth : Nat) : substituteArgs .nil depth ts = ts := by
  cases ts with
  | nil => rfl
  | cons x xs => simp only [substituteArgs, emptySubstitution x, emptyArgsSubstitution xs]
 termination_by sizeOf ts
end

theorem shiftType (t : Expr) (amount cutoff : Nat) :
    (shift amount cutoff t).type = t.type := by
  cases t with
  | free σ x => rfl
  | bound σ i => simp [shift, Expr.type]
  | lam σ body => simp only [shift, Expr.type, shiftType body]
  | head f base => rfl
  | marked f τ base extras => rfl
termination_by sizeOf t
end LogicLineages.PersistentMarking.SubstitutionProof
