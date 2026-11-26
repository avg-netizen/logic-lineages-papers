module
public import LogicLineages.PermittedControl.SignedCongruenceMatrixSliceTargets

@[expose] public section
namespace LogicLineages.PermittedControl.SignedCongruenceMatrixLowStrips
open MixedRankNamedResidueRow (RawArgs)
open SharedRankResidueRow (SourceRow encodeRow)
open SignedCongruenceMatrix (actualRows)
open SignedCongruenceMatrixSlice (RowResult RawResult sliceRows sliceRowsCode encodeResult HitRows)

abbrev Args := Nat × Nat × List RawArgs
abbrev Branch := Nat × List RowResult
abbrev RawBranch := Nat × List RawResult

noncomputable def branchesCode (f : Nat → Nat) (p : Args) : List RawBranch :=
  (List.range p.2.1).map (fun a => (a,sliceRowsCode f (p.1,a,p.2.2)))

noncomputable def branches (f : Nat → Nat) (rank bound : Nat) (rows : List SourceRow) :
    List Branch :=
  (List.range bound).map (fun a => (a,sliceRows f rank a rows))

def encodeBranch (b : Branch) : RawBranch := (b.1,b.2.map encodeResult)

def CodeExact : Prop :=
  (∀ f : Nat → Nat, Computable f → Computable (branchesCode f)) ∧
  (∀ (f : Nat → Nat) (p : Args), (branchesCode f p).map Prod.fst = List.range p.2.1) ∧
  ∀ (f : Nat → Nat) (rank bound : Nat) (rows : List SourceRow),
    branchesCode f (rank,bound,rows.map encodeRow) = (branches f rank bound rows).map encodeBranch

def ResidualRanks : Prop :=
  ∀ (f : Nat → Nat) (rank bound : Nat) (rows residual : List SourceRow) (branch : Branch),
    branch ∈ branches f rank bound rows → HitRows branch.2 residual →
    ∀ r ∈ residual, ∀ t ∈ r.2.2, t.2.rank ≠ rank

/-- The same selected value and the same inherited guard apply across the
entire original and residual matrices. No other raw rank is bounded. -/
def GuardedLowMatrix : Prop :=
  ∀ (f ρ : Nat → Nat) (prior : (Nat → Nat) → Prop) (rank bound : Nat) (rows : List SourceRow),
    (∀ r ∈ rows, 0 < r.1) →
    ((∃ a : Nat, a < bound ∧ prior (Function.update ρ rank a) ∧
        ∃ values : List (List Nat), actualRows f (Function.update ρ rank a) rows values) ↔
      ∃ (branch : Branch) (residual : List SourceRow),
        branch ∈ branches f rank bound rows ∧ HitRows branch.2 residual ∧
        prior (Function.update ρ rank branch.1) ∧
        ∃ values : List (List Nat), actualRows f (Function.update ρ rank branch.1) residual values)

def FullSignedCongruenceMatrixLowStrips : Prop := CodeExact ∧ ResidualRanks ∧ GuardedLowMatrix

end LogicLineages.PermittedControl.SignedCongruenceMatrixLowStrips
