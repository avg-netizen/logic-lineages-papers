module
public import LogicLineages.PermittedControl.OriginalPrintedPlainMatrixOrderBranchesTargets
public import LogicLineages.PermittedControl.OriginalNormalizedMatrixPositiveSnapshotsTargets

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedZeroSupport
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open OriginalPrintedCircuitSequential (Gate)
open OriginalPrintedPlainMatrixInfiniteLow (matrix circuit)
open OriginalPrintedPlainMatrixOrderBranches (SourceAccepts)
open OriginalNormalizedCircuitMatrix (rowsList)
open OriginalPlainTerminalMatrix (readBits)
open OriginalNormalizedMatrixPositiveSnapshots (AllTrue)
open OriginalMatrixDenseRanks (support)
open HeterogeneousSignedMatrixSlice (Row Snapshot actualRows)
open SignedRowGuardedTest (Test)

def admitted : Test → Bool
  | .congruence m => decide (0 < m)
  | _ => true

def bit (test : Test) (v : Int) : Bool :=
  match test with
  | .equalZero => decide (v = 0)
  | .nonnegative => decide (0 ≤ v)
  | .positive => decide (0 < v)
  | .congruence m => decide (v % (m : Int) = 0)

def closedCell : Row → Option (Int × Bool)
  | (test,c,[]) => if admitted test then some (c,bit test c) else none
  | _ => none

def closedSnapshot : List Row → Option Snapshot
  | [] => some []
  | r::rs => do
    let v ← closedCell r
    let tail ← closedSnapshot rs
    pure (v::tail)

def finish (p : NormalForm.Formula) (graph tail : Snapshot) : Option Bool :=
  if graph.all Prod.snd then
    match readBits p (tail.map Prod.snd) with
    | some (b,[]) => some b
    | _ => none
  else none

/-- The normalized typed matrix is the original one. A failed graph or
unadmitted row is None, not a false terminal. Both terminal truth values
are otherwise returned distinctly. -/
noncomputable def answer (known : List Nat) (gates : List Gate) (p : NormalForm.Formula) : Option Bool :=
  do
    let graph ← closedSnapshot (rowsList (circuit known gates p))
    let tail ← closedSnapshot (OriginalPlainTerminalMatrix.rows p)
    finish p graph tail

def ExactClosedActualSnapshot : Prop :=
  ∀ (f ρ : Nat → Nat) (rs : List Row) (snap : Snapshot),
    closedSnapshot rs = some snap ↔
      (∀ r ∈ rs, r.2.2 = []) ∧ actualRows f ρ rs snap

def ExactOriginalZeroSupport : Prop :=
  ∀ (f θ : Nat → Nat) (known : List Nat) (gates : List Gate) (p : NormalForm.Formula),
    PreparedProjection.PlainPreparedFormula p → support (matrix known gates p) = [] →
    ∀ positive : Bool,
      (answer known gates p = some positive ↔ SourceAccepts f θ known gates p positive)

def FullOriginalPrintedZeroSupport : Prop :=
  ExactClosedActualSnapshot ∧ ExactOriginalZeroSupport

end LogicLineages.PermittedControl.OriginalPrintedZeroSupport
