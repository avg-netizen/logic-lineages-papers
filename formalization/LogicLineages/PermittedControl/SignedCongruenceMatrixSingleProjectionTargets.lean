module
public import LogicLineages.PermittedControl.HighTailCongruenceMatrixProjectionTargets
public import LogicLineages.PermittedControl.SignedCongruenceMatrixLowStripsTargets

@[expose] public section
namespace LogicLineages.PermittedControl.SignedCongruenceMatrixSingleProjection
open OrdinalComparison FiniteStripCollectorRecovery
open MixedSameRankResidue (properOperand)
open MixedRankNamedResidueRow (RawArgs)
open SharedRankResidueRow (SourceRow encodeRow commonLayout requests)
open SignedCongruenceMatrix (actualRows commonTail commonTailCode)
open SignedCongruenceMatrixSlice (HitRows)
open SignedCongruenceMatrixLowStrips (Branch RawBranch branches branchesCode encodeBranch)
open HighTailCongruenceMatrixProjection (projectCode projected)

abbrev Args := Nat × Nat × Nat × List RawArgs
abbrev Packet := List RawBranch × (List NamedCode × Nat)

/-- Complete original low status table plus the one actual projected high
formula, using the same effective original common cutoff on both parts. -/
noncomputable def compileCode (f : Nat → Nat) (p : Args) : Option Packet :=
  let (B,name,rank,rows) := p
  (projectCode (B,name,rows)).map
    (fun high => (branchesCode f (rank,commonTailCode B rows,rows),high))

def CodeExact : Prop :=
  (∀ f : Nat → Nat, Computable f → Computable (compileCode f)) ∧
  (∀ (f : Nat → Nat) (B name rank : Nat) (rows : List RawArgs),
    compileCode f (B,name,rank,rows) = none ↔ ∃ r ∈ rows, r.1 = 0) ∧
  ∀ (f : Nat → Nat) (B name rank : Nat) (rows : List SourceRow), (∀ r ∈ rows, 0 < r.1) →
    compileCode f (B,name,rank,rows.map encodeRow) =
      some ((branches f rank (commonTail B rows) rows).map encodeBranch,
        (requests (commonLayout rows)).map encodeRequest,(projected B name rows).encode)

def LowHit (f ρ : Nat → Nat) (B rank : Nat) (rows : List SourceRow) : Prop :=
  ∃ (branch : Branch) (residual : List SourceRow),
    branch ∈ branches f rank (commonTail B rows) rows ∧ HitRows branch.2 residual ∧
      ∃ values : List (List Nat), actualRows f (Function.update ρ rank branch.1) residual values

/-- The original signed-congruence fragment has one unrestricted selected
raw rank, with all other used ranks fixed above the common tail. -/
def ActualJointCaseSplit : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (name rank : Nat) (rows : List SourceRow) (ρ ν : Nat → Nat),
    (name,rank) ∈ commonLayout rows →
    (∀ r ∈ rows, 0 < r.1 ∧ ∀ t ∈ r.2.2, properOperand t.2) →
    (∀ k ∈ (commonLayout rows).map Prod.snd, k ≠ rank → commonTail B rows ≤ ρ k) →
    (∀ s ∈ commonLayout rows, s.1 ≠ name → ν s.1 = ρ s.2) →
    ((∃ z : Nat, ∃ values : List (List Nat), actualRows f (Function.update ρ rank z) rows values) ↔
      LowHit f ρ B rank rows ∨ (projected B name rows).eval ν)

def FullSignedCongruenceMatrixSingleProjection : Prop := CodeExact ∧ ActualJointCaseSplit

end LogicLineages.PermittedControl.SignedCongruenceMatrixSingleProjection
