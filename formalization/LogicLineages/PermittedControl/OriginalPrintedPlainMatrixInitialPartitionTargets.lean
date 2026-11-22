module
public import LogicLineages.PermittedControl.OriginalPrintedPlainMatrixSupportLowTargets

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedPlainMatrixInitialPartition
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open OriginalPrintedCircuitSequential (Gate)
open OriginalPrintedPlainMatrixOrderBranches (branches SourceAccepts)
open OriginalPrintedPlainMatrixInfiniteLow (matrix)
open OriginalMatrixDenseRanks (support)
open OriginalMatrixActualHighPacket (originalFamilyCeiling BranchPacket)
open ActualFiniteOrderBranches (Pattern realized guard)
open OriginalPrintedPlainMatrixSupportLow (LowAt)

noncomputable def names (known : List Nat) (gates : List Gate) (p : NormalForm.Formula) : List Nat :=
  support (matrix known gates p)

def HasSmall (B : Nat) (θ : Nat → Nat) (known : List Nat) (gates : List Gate) (p : NormalForm.Formula) : Prop :=
  ∃ name ∈ names known gates p, θ name < originalFamilyCeiling B known gates p

def NonemptyLarge (B : Nat) (θ : Nat → Nat) (known : List Nat) (gates : List Gate)
    (p : NormalForm.Formula) : Prop :=
  names known gates p ≠ [] ∧
    ∀ name ∈ names known gates p, originalFamilyCeiling B known gates p ≤ θ name

/-- A passing dense branch on nonempty literal support has an actual
source representative at rank zero, whose true value pays the ceiling. -/
def ExactActualRankZeroFunding : Prop :=
  ∀ (B : Nat) (θ : Nat → Nat) (known : List Nat) (gates : List Gate)
    (p : NormalForm.Formula), NonemptyLarge B θ known gates p →
    ∀ branch ∈ branches known gates p, (guard branch).eval θ →
      originalFamilyCeiling B known gates p ≤ realized θ branch 0

def LowCase (f : Nat → Nat) (B : Nat) (θ : Nat → Nat) (known : List Nat) (gates : List Gate)
    (p : NormalForm.Formula) (prior : (Nat → Nat) → Prop) (polarity : Bool) : Prop :=
  ∃ name ∈ names known gates p, θ name < originalFamilyCeiling B known gates p ∧
    LowAt f B θ known gates p prior polarity name

def HighCase (f : Nat → Nat) (B : Nat) (θ : Nat → Nat) (known : List Nat) (gates : List Gate)
    (p : NormalForm.Formula) (prior : (Nat → Nat) → Prop) (polarity : Bool) : Prop :=
  NonemptyLarge B θ known gates p ∧
    ∃ branch ∈ branches known gates p, (guard branch).eval θ ∧ prior θ ∧
      BranchPacket f B θ known gates p polarity branch

def ZeroCoordinateCase (f θ : Nat → Nat) (known : List Nat) (gates : List Gate)
    (p : NormalForm.Formula) (prior : (Nat → Nat) → Prop) (polarity : Bool) : Prop :=
  names known gates p = [] ∧ prior θ ∧ SourceAccepts f θ known gates p polarity

def ExactInitialPartition : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (θ : Nat → Nat) (known : List Nat) (gates : List Gate) (p : NormalForm.Formula),
    PreparedProjection.PlainPreparedFormula p →
    ∀ (prior : (Nat → Nat) → Prop) (polarity : Bool),
      (prior θ ∧ SourceAccepts f θ known gates p polarity) ↔
        LowCase f B θ known gates p prior polarity ∨ HighCase f B θ known gates p prior polarity ∨
          ZeroCoordinateCase f θ known gates p prior polarity

def ExactThreeStrata : Prop :=
  ∀ (B : Nat) (θ : Nat → Nat) (known : List Nat) (gates : List Gate) (p : NormalForm.Formula),
    (HasSmall B θ known gates p ∨ NonemptyLarge B θ known gates p ∨ names known gates p = []) ∧
    (HasSmall B θ known gates p → ¬ NonemptyLarge B θ known gates p) ∧
    (HasSmall B θ known gates p → names known gates p ≠ []) ∧
    (NonemptyLarge B θ known gates p → names known gates p ≠ [])

def FullOriginalPrintedPlainMatrixInitialPartition : Prop :=
  ExactActualRankZeroFunding ∧ ExactThreeStrata ∧ ExactInitialPartition

end LogicLineages.PermittedControl.OriginalPrintedPlainMatrixInitialPartition
