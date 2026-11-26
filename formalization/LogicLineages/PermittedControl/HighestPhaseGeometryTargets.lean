module
public import LogicLineages.PermittedControl.HighestPieceTargets

@[expose] public section
namespace LogicLineages.PermittedControl.Targets
open OrdinalComparison

/-- The actual executable highest-piece selector yields a genuine source
right-closed phase endpoint or an admitted top-clipped-limit witness.
No visit to the arbitrary norm-ball representative is asserted. -/
def HighestPhaseGeometry : Prop := ∀ (mu nu E : NONote) (n : Nat),
  highestPieceCode (rawNoteEncode mu.1) (rawNoteEncode nu.1) (rawNoteEncode E.1)=some n →
  let z := (rawNoteDecode n).repr
  let M := 3+actualOrdinalNorm mu.1.repr+actualOrdinalNorm nu.1.repr+actualOrdinalNorm E.1.repr
  (∃ beta : Ordinal.{0}, 2 ≤ beta ∧ beta < E.1.repr ∧ beta < epsilonZero ∧
    actualOrdinalNorm (beta+1) ≤ M ∧
    SameProfilePiece mu.1.repr nu.1.repr beta z ∧
    relativeProfile mu.1.repr beta ≠ relativeProfile nu.1.repr beta ∧
    (∀ e : Ordinal.{0}, beta < e → e < E.1.repr → relativeProfile mu.1.repr e=relativeProfile nu.1.repr e) ∧
    compare (relativeProfile nu.1.repr beta) (relativeProfile mu.1.repr beta)=
      compare (rawProfileCode (rawNoteEncode nu.1) n) (rawProfileCode (rawNoteEncode mu.1) n)) ∨
  (Order.IsSuccLimit E.1.repr ∧ ∃ zeta : Ordinal.{0}, 2 ≤ zeta ∧ zeta < E.1.repr ∧ zeta < epsilonZero ∧
    actualOrdinalNorm zeta ≤ M ∧
    (∀ e : Ordinal.{0}, zeta ≤ e → e < E.1.repr → SameProfilePiece mu.1.repr nu.1.repr e z) ∧
    relativeProfile mu.1.repr zeta ≠ relativeProfile nu.1.repr zeta ∧
    (∀ e : Ordinal.{0}, zeta ≤ e → e < E.1.repr →
      relativeProfile mu.1.repr e=relativeProfile mu.1.repr zeta ∧
      relativeProfile nu.1.repr e=relativeProfile nu.1.repr zeta) ∧
    compare (relativeProfile nu.1.repr zeta) (relativeProfile mu.1.repr zeta)=
      compare (rawProfileCode (rawNoteEncode nu.1) n) (rawProfileCode (rawNoteEncode mu.1) n))

end LogicLineages.PermittedControl.Targets
