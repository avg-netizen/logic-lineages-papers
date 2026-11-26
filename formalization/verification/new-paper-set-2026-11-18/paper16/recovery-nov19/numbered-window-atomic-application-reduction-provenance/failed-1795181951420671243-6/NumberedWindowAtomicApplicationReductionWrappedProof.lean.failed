module
public import LogicLineages.PersistentMarking.NumberedWindowAtomicApplicationReductionTargets

public section
namespace LogicLineages.PersistentMarking.NumberedWindowAtomicApplicationReductionWrappedProof
open NumberedWindowFieldAlgorithm (unpackNode)
open NumberedWindowRawContextAlgorithm

theorem terminal (root : RawRoot) (fuel : Nat) (value : Bool) :
    iterate root fuel (value,none) = (value,none) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simpa only [iterate,tick] using ih

/-- The actual supplied raw wrapper, not merely existence of another
accepted root code. Atom applications use this at their supplied child. -/
theorem suppliedRoot (root : RawRoot) (fuel q witness y : Nat)
    (no : ∀ tag fs, next tag fs q y = none)
    (h : run root fuel q witness y = true) :
    ∃ cert, unpackNode witness = some (0,[cert]) ∧ root q cert y = true := by
  cases fuel with
  | zero => simp [run,iterate] at h
  | succ fuel =>
    cases seen : unpackNode witness with
    | none => simp [run,iterate,tick,seen,terminal] at h
    | some node =>
      rcases node with ⟨tag,fields⟩
      cases tag with
      | zero =>
        rcases fields with _ | ⟨r,_ | ⟨a,as⟩⟩
        · simp [run,iterate,tick,seen,terminal,no] at h
        · have accepted : root q r y = true := by
            simpa only [run,iterate,tick,seen,terminal] using h
          exact ⟨r,by first | exact seen | rfl,accepted⟩
        · simp [run,iterate,tick,seen,terminal,no] at h
      | succ k => simp [run,iterate,tick,seen,terminal,no] at h

end LogicLineages.PersistentMarking.NumberedWindowAtomicApplicationReductionWrappedProof
