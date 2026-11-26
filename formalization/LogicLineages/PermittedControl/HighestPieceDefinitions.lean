module
public import LogicLineages.PermittedControl.FiniteProfileDefinitions
public import LogicLineages.OrdinalComparison.EncodedNormBallDefinitions

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

/-- A total coded filter, with no semantic predicate hidden in the program. -/
def highestPieceCandidates (mu nu E : Nat) : List Nat :=
  (encodedNormalNormBall (2+rawNormCode mu+rawNormCode nu)).filter (fun e =>
    decide (rawComparisonCode (rawNoteEncode (ONote.ofNat 2)) e ≠ 2 ∧
      rawComparisonCode e E = 0 ∧ rawProfileCode mu e ≠ rawProfileCode nu e))

/-- Select the ordinal-largest code using the already checked raw comparison.
Empty lists return none; invalid raw inputs still have a total output. -/
def chooseLargestProfileCode : List Nat → Option Nat
  | [] => none
  | n::l => match chooseLargestProfileCode l with
    | none => some n
    | some m => some (if rawComparisonCode n m = 2 then n else m)

def highestPieceCode (mu nu E : Nat) : Option Nat :=
  chooseLargestProfileCode (highestPieceCandidates mu nu E)

end LogicLineages.PermittedControl
