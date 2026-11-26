module
public import LogicLineages.PersistentMarking.NumberedWindowAtomicRawStepFieldProof
public section

namespace LogicLineages.PersistentMarking.NumberedWindowAtomicRawStepContextProof
open NumberedWindowAtomicRawStep NumberedWindowAtomicRawStepTargets
open NumberedWindowAtomicRawStepFieldProof (freeView bottomView)
open NumberedWindowFieldAlgorithm (unpackNode)
open NumberedWindowRawContextAlgorithm

private theorem noDescent (tag : Nat) (ws : List Nat) (q y rawTag : Nat) (fields : List Nat)
    (view : unpackNode q = some (rawTag,fields)) (atom : rawTag = 0 ∨ rawTag = 3) :
    next tag ws q y = none := by
  cases hy : unpackNode y with
  | none => simp [next,view,hy]
  | some pair =>
    rcases pair with ⟨destTag,destFields⟩
    rcases atom with rfl | rfl <;>
      rcases tag with _ | _ | _ | _ | _ | _ | tag <;>
      rcases ws with _ | ⟨w,_ | ⟨u,_ | ⟨v,vs⟩⟩⟩ <;>
      simp [next,view,hy,context]

theorem noContext : ExactAtomicNoContextDescent := by
  constructor
  · intro tag ws t n y
    exact noDescent tag ws (freeRaw t n) y 0 [t,n] (freeView t n) (Or.inl rfl)
  · intro tag ws t y
    exact noDescent tag ws (bottomRaw t) y 3 [t] (bottomView t) (Or.inr rfl)

private theorem terminal (root : RawRoot) (fuel : Nat) (value : Bool) :
    iterate root fuel (value,none) = (value,none) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simpa only [iterate,tick] using ih

/-- Inspect the original raw certificate once. A proper context is
impossible at the atom, so a successful tick can only be the literal
original singleton root wrapper. -/
private theorem tickReport (root : RawRoot) (q w y : Nat)
    (no : ∀ tag ws, next tag ws q y = none) :
    ∃ value : Bool, tick root (false,some (q,w,y)) = (value,none) ∧
      (value = true → ∃ v, root q v y = true) := by
  cases hw : unpackNode w with
  | none => exact ⟨false,by simp [tick,hw], by simp⟩
  | some parsed =>
    rcases parsed with ⟨tag,fields⟩
    cases tag with
    | zero =>
      rcases fields with _ | ⟨v,_ | ⟨s,ss⟩⟩
      · exact ⟨false,by simp [tick,hw,no], by simp⟩
      · exact ⟨root q v y,by simp [tick,hw],fun yes => ⟨v,yes⟩⟩
      · exact ⟨false,by simp [tick,hw,no], by simp⟩
    | succ tag =>
      exact ⟨false,by simp [tick,hw,no], by simp⟩

theorem runRoot (root : RawRoot) (fuel q w y : Nat)
    (no : ∀ tag ws, next tag ws q y = none)
    (h : run root fuel q w y = true) : ∃ v, root q v y = true := by
  cases fuel with
  | zero => simp [run,iterate] at h
  | succ fuel =>
    obtain ⟨value,fixed,recover⟩ := tickReport root q w y no
    have accepted : value = true := by
      simpa only [run,iterate,fixed,terminal] using h
    exact recover accepted

end LogicLineages.PersistentMarking.NumberedWindowAtomicRawStepContextProof
