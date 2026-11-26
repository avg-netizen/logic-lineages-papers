import LogicLineages.PersistentMarking.FiniteDomainFoundationTargets
namespace LogicLineages.PersistentMarking.FiniteEqualityProof
open Spine NameBridge FiniteDomainFoundation
mutual
 theorem expr (q r : Expr) : exprEq q r = true ↔ q=r := by
  cases q <;> cases r <;> simp only [exprEq,Bool.and_eq_true,decide_eq_true_eq,reduceCtorEq]
  case lam.lam σ q τ r => rw [expr q r]
  case head.head f qs g rs => rw [args qs rs]
  case marked.marked f σ qs es g τ rs fs => simp only [args qs rs,args es fs,and_assoc]
 termination_by sizeOf q + sizeOf r
 theorem args (qs rs : Args) : argsEq qs rs = true ↔ qs=rs := by
  cases qs <;> cases rs <;> simp only [argsEq,Bool.and_eq_true,reduceCtorEq]
  case cons.cons q qs r rs => rw [expr q r,args qs rs]
 termination_by sizeOf qs + sizeOf rs
end

theorem dedupMem (same : α → α → Bool) (he : ∀ x y, same x y = true ↔ x=y)
    (xs : List α) (q : α) : q ∈ dedupBy same xs ↔ q ∈ xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    by_cases h : xs.any (same x) = true
    · have hx : x ∈ xs := by
        obtain ⟨y,hy,hxy⟩ := List.any_eq_true.mp h
        exact (he x y).mp hxy ▸ hy
      simp only [dedupBy,h,ite_true,ih,List.mem_cons]
      exact ⟨Or.inr,fun hh => hh.elim (fun eq => eq ▸ hx) id⟩
    · simp [dedupBy,h,ih]

theorem dedupDistinct (same : α → α → Bool) (he : ∀ x y, same x y = true ↔ x=y)
    (xs : List α) : (dedupBy same xs).Pairwise (· ≠ ·) := by
  induction xs with
  | nil => exact .nil
  | cons x xs ih =>
    by_cases h : xs.any (same x) = true
    · simpa only [dedupBy,h,ite_true] using ih
    · simp only [dedupBy,if_neg h]
      apply List.Pairwise.cons _ ih
      intro y hy hxy
      apply h
      exact List.any_eq_true.mpr ⟨y,(dedupMem same he xs y).mp hy,(he x y).mpr hxy⟩

theorem observations : FiniteDomainFoundationTargets.ObservationDedup := fun xs =>
  ⟨dedupMem exprEq expr xs,dedupDistinct exprEq expr xs⟩
theorem contexts : FiniteDomainFoundationTargets.ContextDedup := fun xs =>
  ⟨dedupMem _ (fun _ _ => by simp) xs,dedupDistinct _ (fun _ _ => by simp) xs⟩
end LogicLineages.PersistentMarking.FiniteEqualityProof
