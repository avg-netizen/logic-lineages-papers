module
public import LogicLineages.PermittedControl.OriginalPrintedPlainMatrixOrderBranchesTargets
public import LogicLineages.PermittedControl.OriginalMatrixPaidCongruenceTargets

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedPlainMatrixModularBranches
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open OriginalPrintedCircuitSequential (Gate)
open OriginalPrintedPlainMatrixOrderBranches (branches renamed SourceAccepts)
open ActualFiniteOrderBranches (Pattern realized guard)
open OriginalPrintedPlainMatrixInfiniteLow (circuit)
open OriginalNormalizedCircuitMatrix (passingList)
open OriginalMatrixPaidCongruence (enabledRows rankLayout paidRow)
open HeterogeneousSignedMatrixSlice (Snapshot)

/-- Every literal modular row at this initial emission contains only
coordinate occurrences. Identity and norm guards have not disappeared:
they remain separate actual nonmodular graph rows in the prefix. -/
def ExactInitialModularPayment : Prop :=
  ∀ (B : Nat) (ρ : Nat → Nat) (known : List Nat) (gates : List Gate) (p : NormalForm.Formula)
    (branch : Pattern), ∀ r ∈ renamed known gates p branch, paidRow B ρ r

def CompiledAccepts (f θ : Nat → Nat) (known : List Nat) (gates : List Gate)
    (p : NormalForm.Formula) (positive : Bool) (branch : Pattern) : Prop :=
  let rs := renamed known gates p branch
  ∃ suffix : Snapshot, enabledRows f (realized θ branch) (rankLayout rs) rs
    (passingList θ (circuit known gates p) ++ suffix) ∧ OriginalPlainTerminalMatrix.accepts p positive suffix

/-- Original full graph, same guarded order branches and literal terminal
polarity. Only modular snapshots are tested through the residue formula. -/
def ExactPrintedModularBranches : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (θ : Nat → Nat) (known : List Nat) (gates : List Gate) (p : NormalForm.Formula),
    PreparedProjection.PlainPreparedFormula p →
    ∀ (prior : (Nat → Nat) → Prop) (positive : Bool),
      (prior θ ∧ SourceAccepts f θ known gates p positive) ↔
        ∃ branch ∈ branches known gates p, (guard branch).eval θ ∧ prior θ ∧
          CompiledAccepts f θ known gates p positive branch

def FullOriginalPrintedPlainMatrixModularBranches : Prop :=
  ExactInitialModularPayment ∧ ExactPrintedModularBranches

end LogicLineages.PermittedControl.OriginalPrintedPlainMatrixModularBranches
