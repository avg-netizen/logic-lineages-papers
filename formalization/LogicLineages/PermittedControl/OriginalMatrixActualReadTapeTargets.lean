module
public import LogicLineages.PermittedControl.HeterogeneousSignedMatrixSliceTargets
public import LogicLineages.PermittedControl.ActualReadChargeIterationTargets

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalMatrixActualReadTape
open MixedSameRankResidue (WeightedOperand)
open PreparedProjection (lowerOperandRead)
open ActualZeroClassReplacement (Read liftedReads)
open ActualReadChargeIteration (ReadState stateValue)
open HeterogeneousSignedMatrixSlice (Row Snapshot actualRows)
open SignedRowSliceValue (valueAt)

-- Every occurrence is read at its unchanged original coordinate and weight.
-- Both non-hit statuses block the tape, even in a zero or cancelled term.
noncomputable def readTape (f ρ : Nat → Nat) : List WeightedOperand → Option (List Read)
  | [] => some []
  | t :: rest =>
      match lowerOperandRead f ρ t.2 with
      | some (some v) => (readTape f ρ rest).map (fun tail => (t,v) :: tail)
      | _ => none

noncomputable def readState (f ρ : Nat → Nat) (row : Row) : Option ReadState :=
  (readTape f ρ row.2.2).map (fun reads => ⟨row.2.1,reads⟩)

def ExactReadTape : Prop :=
  ∀ (f ρ : Nat → Nat) (terms : List WeightedOperand) (reads : List Read),
    readTape f ρ terms = some reads ↔ reads.map Prod.fst = terms ∧ liftedReads f ρ reads

def ExactRowState : Prop :=
  ∀ (f ρ : Nat → Nat) (row : Row) (v : Int),
    valueAt f ρ row.2.1 row.2.2 v ↔
      ∃ s : ReadState, readState f ρ row = some s ∧ stateValue s = v

def guardedStates (f ρ : Nat → Nat) : List Row → Snapshot → List ReadState → Prop
  | [], [], [] => True
  | row :: rows, v :: vs, s :: ss =>
      row.1.Admitted ∧ readState f ρ row = some s ∧ stateValue s = v.1 ∧
        row.1.atPolarity v.2 v.1 ∧ guardedStates f ρ rows vs ss
  | _, _, _ => False

/-- Source guards (including exact failure of missing fields) and all signed
test outcomes survive one shared valuation and the original row order. -/
def ExactGuardedMatrixTapes : Prop :=
  ∀ (f ρ : Nat → Nat) (rows : List Row) (snap : Snapshot),
    actualRows f ρ rows snap ↔ ∃ states : List ReadState, guardedStates f ρ rows snap states

def FullOriginalMatrixActualReadTape : Prop := ExactReadTape ∧ ExactRowState ∧ ExactGuardedMatrixTapes

end LogicLineages.PermittedControl.OriginalMatrixActualReadTape
