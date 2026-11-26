module
public import LogicLineages.PermittedControl.OriginalPrintedPlainMatrixOrderBranchesTargets
public import LogicLineages.PermittedControl.OriginalNormalizedMatrixPositiveSnapshotsTargets

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedTerminalBitClauses
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open HeterogeneousSignedMatrixSlice (Row Snapshot actualRows)
open SignedRowSliceValue (valueAt)
open OriginalPlainTerminalMatrix (readBits accepts)
open OriginalNormalizedMatrixPositiveSnapshots (AllTrue)
open OriginalPrintedCircuitSequential (Gate)
open OriginalPrintedPlainMatrixOrderBranches (SourceAccepts)
open OriginalPrintedPlainMatrixInfiniteLow (circuit)
open PreparedProjection (PlainPreparedFormula)

abbrev BitRow := Row × Bool

def vectors : Nat → List (List Bool)
  | 0 => [[]]
  | n+1 => (vectors n).map (List.cons false) ++ (vectors n).map (List.cons true)

def accepted (p : NormalForm.Formula) (positive : Bool) (n : Nat) : List (List Bool) :=
  (vectors n).filter (fun bits => decide (readBits p bits = some (positive,[])))

def zipBits : List Row → List Bool → List BitRow
  | r::rs,b::bs => (r,b)::zipBits rs bs
  | _,_ => []

def clauses (pre tail : List Row) (p : NormalForm.Formula) (positive : Bool) : List (List BitRow) :=
  (accepted p positive tail.length).map (fun bits => (pre.map (fun row => (row,true))) ++ zipBits tail bits)

def RowHolds (f ρ : Nat → Nat) (r : BitRow) : Prop :=
  r.1.1.Admitted ∧ ∃ v : Int, valueAt f ρ r.1.2.1 r.1.2.2 v ∧ r.1.1.atPolarity r.2 v

def ClauseHolds (f ρ : Nat → Nat) (rows : List BitRow) : Prop :=
  ∀ row ∈ rows, RowHolds f ρ row

def ExactAcceptedVectors : Prop :=
  ∀ (p : NormalForm.Formula) (positive : Bool) (n : Nat) (bits : List Bool),
    bits ∈ accepted p positive n ↔
      bits.length = n ∧ readBits p bits = some (positive,[])

def ExactBitTape : Prop :=
  ∀ (f ρ : Nat → Nat) (rows : List Row) (bits : List Bool), bits.length = rows.length →
    (ClauseHolds f ρ (zipBits rows bits) ↔
      ∃ snap : Snapshot, actualRows f ρ rows snap ∧ snap.map Prod.snd = bits)

def ExactPositivePrefixAndBooleanSuffix : Prop :=
  ∀ (f ρ : Nat → Nat) (pre tail : List Row) (p : NormalForm.Formula) (positive : Bool),
    ((∃ prefixSnap : Snapshot, actualRows f ρ pre prefixSnap ∧ AllTrue prefixSnap) ∧
      ∃ suffix : Snapshot, actualRows f ρ tail suffix ∧ accepts p positive suffix) ↔
    ∃ branch ∈ clauses pre tail p positive, ClauseHolds f ρ branch

/-- Positive original graph rows are emitted verbatim; only the exact
ordered original terminal Boolean syntax selects the signed suffix bits. -/
def ExactPrintedNormalizedBoolClauses : Prop :=
  ∀ (f θ : Nat → Nat) (known : List Nat) (gates : List Gate) (p : NormalForm.Formula),
    PlainPreparedFormula p → ∀ positive : Bool,
      (SourceAccepts f θ known gates p positive ↔
        ∃ branch ∈ clauses (OriginalNormalizedCircuitMatrix.rowsList (circuit known gates p))
          (OriginalPlainTerminalMatrix.rows p) p positive, ClauseHolds f θ branch)

def FullOriginalPrintedTerminalBitClauses : Prop :=
  ExactAcceptedVectors ∧ ExactBitTape ∧ ExactPositivePrefixAndBooleanSuffix ∧ ExactPrintedNormalizedBoolClauses

end LogicLineages.PermittedControl.OriginalPrintedTerminalBitClauses
