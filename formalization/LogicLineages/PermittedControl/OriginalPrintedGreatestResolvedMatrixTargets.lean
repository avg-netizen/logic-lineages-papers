module
public import LogicLineages.PermittedControl.OriginalPrintedGreatestGateResolutionTargets
public import LogicLineages.PermittedControl.ClosedOrdinaryFieldTargets

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedGreatestResolvedMatrix
open OrdinalComparison FieldComparison PreparedProjection
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open OriginalPrintedGreatestGateResolution (Mode plan resolutionMinimum)
open OriginalPrintedCircuitSequential (Gate)
open OriginalPrintedPlainMatrixOrderBranches (branches SourceAccepts)
open OriginalPrintedPlainMatrixLinearProjection (top replay)
open OriginalMatrixLinearLowerTable (TopLinear)
open OriginalMatrixDenseRanks (support renameRow)
open OriginalPrintedPlainMatrixInfiniteLow (matrix)
open ActualFiniteOrderBranches (Pattern rename guard)
open HeterogeneousSignedMatrixSlice (Row Snapshot actualRows)
open OriginalNormalizedMatrixPositiveSnapshots (AllTrue)

/-- Static proper shape via the existing closed entry admission guard at the
literal endpoint norm. Its real affordability test remains a separate row. -/
def shortShape (lam mu : NONote) : Row :=
  let l := rawNoteEncode lam.1
  let m := rawNoteEncode mu.1
  (.equalZero,if closedProperEntryGuard (l,m,rawNormCode l) then 0 else 1,[])

def shortValue (lam mu : NONote) (o : Nat) : Row :=
  (.equalZero,(shortGapLength lam mu : Int),[(-1,.coordinate o)])

noncomputable def emit : Mode → List Row
  | .keep (.field (.iterate 0 s o)) => [OriginalFieldGateMatrix.equalityRow (.coordinate s) o]
  | .keep g => OriginalNormalizedCircuitMatrix.rows g
  | .impossible => OriginalNormalizedCircuitMatrix.failedRows
  | .shortCount lam mu s o =>
      [shortShape lam mu,OriginalFieldGateMatrix.identityAffordRow lam s,shortValue lam mu o]

/-- Each gate's emitted rows are contiguous and in original gate order. The
literal signed terminal, including all duplicate atoms, is not rewritten. -/
noncomputable def prefixRows (known : List Nat) (gates : List Gate)
    (p : NormalForm.Formula) (branch : Pattern) : List Row :=
  (plan known gates p branch).flatMap emit

noncomputable def fullRows (known : List Nat) (gates : List Gate)
    (p : NormalForm.Formula) (branch : Pattern) : List Row :=
  prefixRows known gates p branch ++ OriginalPlainTerminalMatrix.rows p

def PositiveRows (f θ : Nat → Nat) (rs : List Row) : Prop :=
  ∃ vs : Snapshot, actualRows f θ rs vs ∧ AllTrue vs

/-- Graph failure cannot be negated with the terminal. Both Boolean outcomes
use the same positive prefix and unchanged original signed suffix snapshot. -/
def PacketAccepts (f θ : Nat → Nat) (pre : List Row) (p : NormalForm.Formula)
    (positive : Bool) : Prop :=
  PositiveRows f θ pre ∧
    ∃ values : Snapshot, actualRows f θ (OriginalPlainTerminalMatrix.rows p) values ∧
      OriginalPlainTerminalMatrix.accepts p positive values

def ExactModeMatrix : Prop :=
  ∀ (f θ : Nat → Nat) (m : Mode), PositiveRows f θ (emit m) ↔ m.Holds f θ

def ExactUniformResolvedMatrix : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (θ : Nat → Nat) (known : List Nat) (gates : List Gate) (p : NormalForm.Formula),
    PlainPreparedFormula p →
    ∀ branch ∈ branches known gates p, (guard branch).eval θ →
      ∀ z : Nat, resolutionMinimum B θ known gates p branch ≤ z →
        ∀ (prior : (Nat → Nat) → Prop) (positive : Bool),
          let ν := replay θ known gates p branch z
          (prior ν ∧ SourceAccepts f ν known gates p positive ↔
            prior ν ∧ PacketAccepts f ν (prefixRows known gates p branch) p positive)

def ExactResolvedMatrixTopLinear : Prop :=
  ∀ (θ : Nat → Nat) (known : List Nat) (gates : List Gate) (p : NormalForm.Formula),
    ∀ branch ∈ branches known gates p, (guard branch).eval θ →
      (∀ n ∈ support (fullRows known gates p branch), n ∈ support (matrix known gates p)) ∧
      TopLinear (top branch) ((fullRows known gates p branch).map (renameRow (rename branch)))

def FullOriginalPrintedGreatestResolvedMatrix : Prop :=
  ExactModeMatrix ∧ ExactUniformResolvedMatrix ∧ ExactResolvedMatrixTopLinear

end LogicLineages.PermittedControl.OriginalPrintedGreatestResolvedMatrix
