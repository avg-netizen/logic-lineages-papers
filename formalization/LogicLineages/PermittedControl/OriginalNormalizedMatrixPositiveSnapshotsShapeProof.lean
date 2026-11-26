module
public import LogicLineages.PermittedControl.OriginalNormalizedMatrixPositiveSnapshotsTargets

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalNormalizedMatrixPositiveSnapshots
open HeterogeneousSignedMatrixSlice (Row Snapshot actualRows)
open MixedSameRankResidue (WeightedOperand)

theorem allAppend (xs ys : Snapshot) :
    AllTrue (xs ++ ys) ↔ AllTrue xs ∧ AllTrue ys := by
  constructor
  · intro h
    exact ⟨fun v inXs => h v (List.mem_append_left _ inXs),
      fun v inYs => h v (List.mem_append_right _ inYs)⟩
  · rintro ⟨h₁,h₂⟩ v atEither
    exact (List.mem_append.mp atEither).elim (h₁ v) (h₂ v)

theorem splitActual (f θ : Nat → Nat) (pre tail : List Row) (snap : Snapshot)
    (live : actualRows f θ (pre ++ tail) snap) :
    ∃ xs ys : Snapshot, snap = xs ++ ys ∧ actualRows f θ pre xs ∧ actualRows f θ tail ys := by
  induction pre generalizing snap with
  | nil => exact ⟨[],snap,rfl,True.intro,live⟩
  | cons row pre ih =>
      cases snap with
      | nil => exact False.elim live
      | cons v vs =>
          obtain ⟨xs,ys,eq,h₁,h₂⟩ := ih vs live.2.2.2
          exact ⟨v :: xs,ys,congrArg (List.cons v) eq,⟨live.1,live.2.1,live.2.2.1,h₁⟩,h₂⟩

theorem oneEq (f θ : Nat → Nat) (c : Int) (ts : List WeightedOperand) (snap : Snapshot)
    (live : actualRows f θ [(.equalZero,c,ts)] snap) (yes : AllTrue snap) :
    snap = [(0,true)] := by
  cases snap with
  | nil => exact False.elim live
  | cons v vs =>
      cases vs with
      | cons w ws => exact False.elim live.2.2.2
      | nil =>
          have bit := yes v List.mem_cons_self
          have value := live.2.2.1
          change (if v.2 then v.1 = 0 else ¬ v.1 = 0) at value
          rw [bit] at value
          have same : v = (0,true) := Prod.ext value bit
          rw [same]

theorem threeTrueShape (f θ : Nat → Nat) (r s t : Row) (snap : Snapshot)
    (live : actualRows f θ [r,s,t] snap) (yes : AllTrue snap) :
    ∃ a b c : Int, snap = [(a,true),(b,true),(c,true)] ∧
      actualRows f θ [r] [(a,true)] ∧ actualRows f θ [s] [(b,true)] ∧ actualRows f θ [t] [(c,true)] := by
  cases snap with
  | nil => exact False.elim live
  | cons x snap =>
      cases snap with
      | nil => exact False.elim live.2.2.2
      | cons y snap =>
          cases snap with
          | nil => exact False.elim live.2.2.2.2.2.2
          | cons z snap =>
              cases snap with
              | cons w ws => exact False.elim live.2.2.2.2.2.2.2.2.2
              | nil =>
                  have xeq : x = (x.1,true) := Prod.ext rfl (yes x List.mem_cons_self)
                  have yeq : y = (y.1,true) := Prod.ext rfl (yes y (by simp))
                  have zeq : z = (z.1,true) := Prod.ext rfl (yes z (by simp))
                  have h₁ : actualRows f θ [r] [x] := ⟨live.1,live.2.1,live.2.2.1,True.intro⟩
                  have hy := live.2.2.2
                  have h₂ : actualRows f θ [s] [y] := ⟨hy.1,hy.2.1,hy.2.2.1,True.intro⟩
                  have h₃ : actualRows f θ [t] [z] := hy.2.2.2
                  exact ⟨x.1,y.1,z.1,by rw [← xeq,← yeq,← zeq],
                    xeq ▸ h₁,yeq ▸ h₂,zeq ▸ h₃⟩

end LogicLineages.PermittedControl.OriginalNormalizedMatrixPositiveSnapshots
