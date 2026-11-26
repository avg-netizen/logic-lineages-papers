module
public import LogicLineages.PermittedControl.HighestPieceDefinitions
public import Mathlib.Computability.Primrec.Basic

@[expose] public section
namespace LogicLineages.PermittedControl.Targets
open OrdinalComparison

/-- Actual source CNF-weight bound for the previously proved cover. -/
def JointProfileCoverBound : Prop := ∀ mu nu E : Ordinal.{0},
  mu < epsilonZero → nu < epsilonZero → E < epsilonZero →
  ∀ y ∈ jointProfileRepresentatives mu nu E,
    y < epsilonZero ∧ actualOrdinalNorm y ≤ 2+actualOrdinalNorm mu+actualOrdinalNorm nu

/-- Exact joint-piece order, not just coincidental equality of numerical costs. -/
def JointProfilePieceOrder : Prop := ∀ mu nu x y z : Ordinal.{0},
  y < x → ¬ SameProfilePiece mu nu x y → SameProfilePiece mu nu x z → y < z

def HighestPieceEffective : Prop :=
  Primrec (fun p : Nat × Nat × Nat => highestPieceCode p.1 p.2.1 p.2.2)

/-- Empty means agreement throughout the full clipped domain, including E<=2. -/
def HighestPieceNone : Prop := ∀ mu nu E : NONote,
  highestPieceCode (rawNoteEncode mu.1) (rawNoteEncode nu.1) (rawNoteEncode E.1) = none ↔
    ∀ x : Ordinal.{0}, 2 ≤ x → x < E.1.repr →
      relativeProfile mu.1.repr x = relativeProfile nu.1.repr x

/-- The literal selected code is a normal bounded candidate and its piece is
highest among all nonzero pieces, including unbounded top-clipped pieces.
No actual descent visit to this arbitrary bounded representative is asserted. -/
def HighestPieceSome : Prop := ∀ (mu nu E : NONote) (n : Nat),
  highestPieceCode (rawNoteEncode mu.1) (rawNoteEncode nu.1) (rawNoteEncode E.1) = some n →
  ONote.NF (rawNoteDecode n) ∧
  (rawNoteDecode n).repr < epsilonZero ∧
  actualOrdinalNorm (rawNoteDecode n).repr ≤
    2+actualOrdinalNorm mu.1.repr+actualOrdinalNorm nu.1.repr ∧
  2 ≤ (rawNoteDecode n).repr ∧ (rawNoteDecode n).repr < E.1.repr ∧
  relativeProfile mu.1.repr (rawNoteDecode n).repr ≠
    relativeProfile nu.1.repr (rawNoteDecode n).repr ∧
  (∀ m ∈ highestPieceCandidates (rawNoteEncode mu.1) (rawNoteEncode nu.1) (rawNoteEncode E.1),
    (rawNoteDecode m).repr ≤ (rawNoteDecode n).repr) ∧
  (∀ x : Ordinal.{0}, 2 ≤ x → x < E.1.repr →
    relativeProfile mu.1.repr x ≠ relativeProfile nu.1.repr x →
    (rawNoteDecode n).repr < x → SameProfilePiece mu.1.repr nu.1.repr x (rawNoteDecode n).repr) ∧
  (∀ x : Ordinal.{0}, SameProfilePiece mu.1.repr nu.1.repr x (rawNoteDecode n).repr →
    compare (relativeProfile nu.1.repr x) (relativeProfile mu.1.repr x) =
    compare (rawProfileCode (rawNoteEncode nu.1) n) (rawProfileCode (rawNoteEncode mu.1) n))

def HighestPieceFoundation : Prop := JointProfileCoverBound ∧ JointProfilePieceOrder ∧
  HighestPieceEffective ∧ HighestPieceNone ∧ HighestPieceSome

end LogicLineages.PermittedControl.Targets
