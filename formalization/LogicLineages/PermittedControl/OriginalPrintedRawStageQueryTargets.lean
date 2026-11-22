module
public import LogicLineages.PermittedControl.OriginalPrintedRawConditionalQueryTargets
public import LogicLineages.PermittedControl.ActualRawStageCutoffTargets

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedRawStageQuery
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open OriginalPrintedCircuitSequential (Gate Topological)
open PreparedProjection (PlainPreparedFormula)
open OriginalPrintedRawFamilyFrontend (Args encodeInput familyCode)
open OriginalPrintedTypedExistential (HasSuccessfulObservation)
open OriginalPrintedRawConditionalQuery (EverySuccessfulObservation)
open ActualBitFamilyRawDriver (HighProgram)
open ActualBitFamilyRawSemanticDriver (TypedHigh)
open ActualRawStageCutoff (stageBound)
open ActualBitFamilyRawLayout (encodeFamily)
open ActualGuardedResidualBitFamily (Family Holds)
open ActualBitFamilyLowSlices (dimension)
open ActualBitFamilyExistentialLow (Satisfiable)
open ActualBitFamilyHigh (AllPaid)

/-- The high callback's remaining obligations at the actual executable
cutoff, with no independently supplied numerical majorant. -/
def HighAtStage (f : Nat → Nat) (B : Nat) (high : HighProgram) (children : TypedHigh) : Prop :=
  ∀ fs : Family, 0 < dimension fs →
    let raw := encodeFamily fs
    let C := stageBound B raw
    high (C,raw) = (children fs).map encodeFamily ∧
    (∀ ch ∈ children fs, dimension ch < dimension fs) ∧
    ((∃ ρ : Nat → Nat, AllPaid C fs ρ ∧ Holds f ρ fs) ↔
      ∃ ch ∈ children fs, Satisfiable f ch)

noncomputable def result (f : Nat → Nat) (B : Nat) (high : HighProgram) (p : Args) :
    Option Bool := OriginalPrintedRawConditionalQuery.result f (stageBound B) high p

def ExactOriginalRawStageQuery : Prop :=
  ∀ (f : Nat → Nat) (B : Nat) (high : HighProgram) (children : TypedHigh),
    HighAtStage f B high children →
    ∀ (known : List Nat) (gs : List Gate) (p : NormalForm.Formula),
      Topological known gs → PlainPreparedFormula p → ∀ positive : Bool,
        (result f B high (encodeInput known gs p positive) = some true ↔
          HasSuccessfulObservation f gs p positive) ∧
        (result f B high (encodeInput known gs p positive) = some false ↔
          ¬ HasSuccessfulObservation f gs p positive) ∧
        (result f B high (encodeInput known gs p (!positive)) = some false ↔
          EverySuccessfulObservation f gs p positive)

def ExactOriginalRawStageFailure : Prop :=
  ∀ (f : Nat → Nat) (B : Nat) (high : HighProgram) (p : Args),
    result f B high p = none ↔ familyCode p = none

def OriginalRawStageQueryEffectivity : Prop :=
  ∀ (f : Nat → Nat) (B : Nat) (high : HighProgram),
    Computable f → Computable high → Computable (result f B high)

def FullOriginalRawStageQuery : Prop :=
  ExactOriginalRawStageQuery ∧ ExactOriginalRawStageFailure ∧ OriginalRawStageQueryEffectivity

end LogicLineages.PermittedControl.OriginalPrintedRawStageQuery
