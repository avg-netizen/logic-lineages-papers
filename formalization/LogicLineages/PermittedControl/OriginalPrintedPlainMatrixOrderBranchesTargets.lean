module
public import LogicLineages.PermittedControl.ActualFiniteOrderBranchesTargets
public import LogicLineages.PermittedControl.OriginalMatrixDenseRanksTargets
public import LogicLineages.PermittedControl.OriginalPrintedPlainMatrixInfiniteLowTargets

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedPlainMatrixOrderBranches
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open OriginalPrintedCircuitSequential (Gate)
open OriginalPrintedCircuitNormalization (Holds)
open OriginalPrintedPlainMatrixInfiniteLow (circuit matrix)
open OriginalNormalizedCircuitMatrix (passingList)
open OriginalMixedTerminalTest (Test)
open OriginalMatrixDenseRanks (support renameRow)
open ActualFiniteOrderBranches (Pattern patterns guard rename realized)
open HeterogeneousSignedMatrixSlice (Row Snapshot actualRows)

noncomputable def branches (known : List Nat) (gates : List Gate) (p : NormalForm.Formula) : List Pattern :=
  patterns (support (matrix known gates p))

noncomputable def renamed (known : List Nat) (gates : List Gate) (p : NormalForm.Formula)
    (branch : Pattern) : List Row :=
  (matrix known gates p).map (renameRow (rename branch))

def SourceAccepts (f θ : Nat → Nat) (known : List Nat) (gates : List Gate)
    (p : NormalForm.Formula) (positive : Bool) : Prop :=
  Holds f θ (circuit known gates p) ∧ (Test.rows p).atPolarity positive θ

def BranchAccepts (f θ : Nat → Nat) (known : List Nat) (gates : List Gate)
    (p : NormalForm.Formula) (positive : Bool) (branch : Pattern) : Prop :=
  ∃ suffix : Snapshot,
    actualRows f (realized θ branch) (renamed known gates p branch)
      (passingList θ (circuit known gates p) ++ suffix) ∧
    OriginalPlainTerminalMatrix.accepts p positive suffix

/-- A branch's own real linear guard derives the shared increasing rank
valuation; both terminal polarities keep it and the source graph positive. -/
def ExactPrintedOrderBranch : Prop :=
  ∀ (f θ : Nat → Nat) (known : List Nat) (gates : List Gate)
    (p : NormalForm.Formula), PreparedProjection.PlainPreparedFormula p →
    ∀ (positive : Bool) (branch : Pattern), branch ∈ branches known gates p → (guard branch).eval θ →
      StrictMono (realized θ branch) ∧
      (∀ row ∈ renamed known gates p branch, ∀ t ∈ row.2.2,
        t.2.rank < branch.1 ∧ t.2.rank ≤ branch.1 - 1) ∧
      (SourceAccepts f θ known gates p positive ↔ BranchAccepts f θ known gates p positive branch)

def ExactPrintedOrderBranchesCover : Prop :=
  ∀ (f θ : Nat → Nat) (known : List Nat) (gates : List Gate)
    (p : NormalForm.Formula), PreparedProjection.PlainPreparedFormula p →
    ∀ (prior : (Nat → Nat) → Prop) (positive : Bool),
      (prior θ ∧ SourceAccepts f θ known gates p positive) ↔
        ∃ branch ∈ branches known gates p, (guard branch).eval θ ∧
          prior θ ∧ BranchAccepts f θ known gates p positive branch

def FullOriginalPrintedPlainMatrixOrderBranches : Prop :=
  ExactPrintedOrderBranch ∧ ExactPrintedOrderBranchesCover

end LogicLineages.PermittedControl.OriginalPrintedPlainMatrixOrderBranches
