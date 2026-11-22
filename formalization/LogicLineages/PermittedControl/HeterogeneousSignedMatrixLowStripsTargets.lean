module
public import LogicLineages.PermittedControl.HeterogeneousSignedMatrixSliceTargets

@[expose] public section
namespace LogicLineages.PermittedControl.HeterogeneousSignedMatrixLowStrips
open HeterogeneousSignedMatrixSlice
  (Row RawRow RowResult RawResult Snapshot encodeRow encodeResult sliceRows sliceRowsCode HitRows actualRows)

abbrev Args := Nat × Nat × List RawRow
abbrev Branch := Nat × List RowResult
abbrev RawBranch := Nat × List RawResult

noncomputable def branchesCode (f : Nat → Nat) (p : Args) : List RawBranch :=
  (List.range p.2.1).map (fun a => (a,sliceRowsCode f (p.1,a,p.2.2)))

noncomputable def branches (f : Nat → Nat) (rank bound : Nat) (rows : List Row) : List Branch :=
  (List.range bound).map (fun a => (a,sliceRows f rank a rows))

def encodeBranch (b : Branch) : RawBranch := (b.1,b.2.map encodeResult)

def CodeExact : Prop :=
  (∀ f : Nat → Nat, Computable f → Computable (branchesCode f)) ∧
  (∀ (f : Nat → Nat) (p : Args), (branchesCode f p).map Prod.fst = List.range p.2.1) ∧
  ∀ (f : Nat → Nat) (rank bound : Nat) (rows : List Row),
    branchesCode f (rank,bound,rows.map encodeRow) = (branches f rank bound rows).map encodeBranch

def ExactBranch : Prop :=
  ∀ (f : Nat → Nat) (rank bound : Nat) (rows : List Row) (branch : Branch),
    branch ∈ branches f rank bound rows ↔
      branch.1 < bound ∧ branch.2 = sliceRows f rank branch.1 rows

/-- One common selected raw value across every row, with the same
updated original valuation at both the inherited guard and the test. -/
def ExactGuardedLowExistential : Prop :=
  ∀ (f ρ : Nat → Nat) (prior : (Nat → Nat) → Prop)
    (rank bound : Nat) (rows : List Row) (test : (Nat → Nat) → Snapshot → Prop) (positive : Bool),
    ((∃ a : Nat, a < bound ∧
      let θ := Function.update ρ rank a
      prior θ ∧ ∃ values : Snapshot, actualRows f θ rows values ∧
        (if positive then test θ values else ¬ test θ values)) ↔
      ∃ (branch : Branch) (residual : List Row),
        branch ∈ branches f rank bound rows ∧ HitRows branch.2 residual ∧
        let θ := Function.update ρ rank branch.1
        prior θ ∧ ∃ values : Snapshot, actualRows f θ residual values ∧
          (if positive then test θ values else ¬ test θ values))

def FullHeterogeneousSignedMatrixLowStrips : Prop :=
  CodeExact ∧ ExactBranch ∧ ExactGuardedLowExistential

end LogicLineages.PermittedControl.HeterogeneousSignedMatrixLowStrips
