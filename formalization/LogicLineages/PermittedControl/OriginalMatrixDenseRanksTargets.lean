module
public import LogicLineages.PermittedControl.ActualCoordinateRankChartTargets
public import LogicLineages.PermittedControl.OriginalMatrixActualReadTapeTargets

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalMatrixDenseRanks
open PreparedProjection (LowerOperand lowerOperandRead LowerOperandActual)
open MixedSameRankResidue (WeightedOperand)
open ActualZeroClassReplacement (Read)
open HeterogeneousSignedMatrixSlice (Row Snapshot actualRows)
open OriginalMatrixActualReadTape (readTape)
open ActualCoordinateRankChart (rankOf rankValue size)

def renameOperand (rename : Nat → Nat) : LowerOperand → LowerOperand
  | .coordinate name => .coordinate (rename name)
  | .ordinary name field => .ordinary (rename name) field
  | .count name lam mu => .count (rename name) lam mu

def renameTerm (rename : Nat → Nat) (t : WeightedOperand) : WeightedOperand :=
  (t.1,renameOperand rename t.2)

def renameRead (rename : Nat → Nat) (rd : Read) : Read :=
  (renameTerm rename rd.1,rd.2)

def renameRow (rename : Nat → Nat) (r : Row) : Row :=
  (r.1,r.2.1,r.2.2.map (renameTerm rename))

/-- Every literal operand name, including repeated and cancelled
occurrences, in original row and operand order. -/
def support (rows : List Row) : List Nat :=
  rows.flatMap (fun r => r.2.2.map (fun t => t.2.rank))

noncomputable def denseRows (θ : Nat → Nat) (rows : List Row) : List Row :=
  rows.map (renameRow (rankOf θ (support rows)))

/-- Works also for noncanonical charts whose actual values are tied.
The original two non-hit statuses are preserved, not replaced by false. -/
def ExactRenamedReadTape : Prop :=
  (∀ (f θ σ rename : Nat → Nat) (op : LowerOperand), σ (rename op.rank) = θ op.rank →
    (renameOperand rename op).rank = rename op.rank ∧
    lowerOperandRead f σ (renameOperand rename op) = lowerOperandRead f θ op ∧
    ∀ v : Nat, LowerOperandActual f σ (renameOperand rename op) v ↔ LowerOperandActual f θ op v) ∧
  ∀ (f θ σ rename : Nat → Nat) (terms : List WeightedOperand),
    (∀ t ∈ terms, σ (rename t.2.rank) = θ t.2.rank) →
    readTape f σ (terms.map (renameTerm rename)) =
      (readTape f θ terms).map (List.map (renameRead rename))

def ExactRenamedMatrix : Prop :=
  ∀ (f θ σ rename : Nat → Nat) (rows : List Row),
    (∀ name ∈ support rows, σ (rename name) = θ name) →
    ∀ values : Snapshot,
      actualRows f σ (rows.map (renameRow rename)) values ↔ actualRows f θ rows values

/-- The straight-line literal packet is unchanged except for raw names.
It has exactly the original test kinds and constants in their original
positions, and every occurrence is within the actual dense finite chart. -/
def ExactDenseMatrix : Prop :=
  ∀ (f θ : Nat → Nat) (rows : List Row),
    let names := support rows
    let σ := rankValue θ names
    let renamed := denseRows θ rows
    StrictMono σ ∧
    renamed.map (fun r => (r.1,r.2.1)) = rows.map (fun r => (r.1,r.2.1)) ∧
    support renamed = names.map (rankOf θ names) ∧
    (∀ k ∈ support renamed, k < size θ names) ∧
    ∀ values : Snapshot, actualRows f σ renamed values ↔ actualRows f θ rows values

def FullOriginalMatrixDenseRanks : Prop :=
  ExactRenamedReadTape ∧ ExactRenamedMatrix ∧ ExactDenseMatrix

end LogicLineages.PermittedControl.OriginalMatrixDenseRanks
