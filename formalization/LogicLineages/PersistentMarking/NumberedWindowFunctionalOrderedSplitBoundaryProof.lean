module

public import LogicLineages.PersistentMarking.NumberedWindowDirectAlgorithm

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowFunctionalOrderedSplitBoundaryProof
open NumberedWindowDirectAlgorithm (Witness directLists)
open NumberedWindowFieldAlgorithm (pack)

def allScalars : Nat → Bool := fun _ => true
def noInsertions : Nat → Nat → Nat → Bool := fun _ _ _ => false

/-- List-level option for each component in the split formula:
literal equality, or the actual certified replacement with insertions
disabled. This statement is about directLists, not dCore calibration. -/
def DeletionOrUnchanged (before after : List Nat) : Prop :=
  before = after ∨ ∃ w : Witness, directLists allScalars noInsertions before after w = true

theorem deletionMembership (before after : List Nat) (h : DeletionOrUnchanged before after)
    (x : Nat) (mem : x ∈ after) : x ∈ before := by
  rcases h with eq | ⟨w,h⟩
  · exact eq ▸ mem
  · simp only [directLists,Bool.and_eq_true] at h
    rcases h with ⟨⟨⟨⟨⟨_,_⟩,src⟩,dst⟩,_⟩,added⟩
    have nothing : w.2.2 = [] := by
      cases hList : w.2.2 with
      | nil => rfl
      | cons e es => simp [hList,noInsertions] at added
    have hp := of_decide_eq_true src
    have hq := of_decide_eq_true dst
    have inKept : x ∈ w.1 := by simpa only [nothing,List.map_nil,List.append_nil] using hq.mem_iff.mp mem
    exact hp.mem_iff.mpr (List.mem_append_left _ inKept)

theorem exact_ReorderedDeletionAccepted :
    directLists allScalars noInsertions [0,0,1] [1,0] ([1,0],[0],[]) = true := by decide

/-- The independently justified sides of the exact ordered split cannot
recombine to the accepted successor, even if both sides are allowed
to remain unchanged. The required strict-side premise would only
restrict this set of impossible candidates further. -/
theorem exact_NoOrderedRecombination (a b : List Nat)
    (left : DeletionOrUnchanged [0,0] a) (right : DeletionOrUnchanged [1] b) :
    a ++ b ≠ [1,0] := by
  intro h
  cases a with
  | nil =>
    have e : b = [1,0] := h
    have bad : (0 : Nat) ∈ [1] := deletionMembership [1] b right 0 (by simp [e])
    simp at bad
  | cons x xs =>
    have hx : x = 1 := (List.cons.inj h).1
    have bad : (1 : Nat) ∈ [0,0] :=
      deletionMembership [0,0] (x::xs) left 1 (by simp [hx])
    simp at bad

theorem exact_ReorderedRawCodes :
    pack [0,0] = 2 ∧ pack [1] = 3 ∧ pack [0,0,1] = 101 ∧
      pack [1,0] = 6 ∧ pack [0,1] = 10 := by
  decide

#print axioms exact_ReorderedDeletionAccepted
#print axioms exact_NoOrderedRecombination
#print axioms exact_ReorderedRawCodes
end LogicLineages.PersistentMarking.NumberedWindowFunctionalOrderedSplitBoundaryProof
