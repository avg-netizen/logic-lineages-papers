module
public import LogicLineages.PermittedControl.OriginalMatrixLowDimensionCodeTargets
public import LogicLineages.PermittedControl.OriginalPrintedPlainMatrixInitialPartitionTargets

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedPlainMatrixDecreasingLow
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open OriginalPrintedCircuitSequential (Gate)
open OriginalPrintedPlainMatrixInfiniteLow (matrix circuit)
open OriginalPrintedPlainMatrixOrderBranches (SourceAccepts)
open OriginalPrintedPlainMatrixInitialPartition (names LowCase HighCase ZeroCoordinateCase)
open OriginalMatrixActualHighPacket (originalFamilyCeiling)
open OriginalNormalizedCircuitMatrix (passingList)
open OriginalMatrixLowDimension (dimension supportSet)
open HeterogeneousSignedMatrixSlice (Snapshot actualRows HitRows RawRow encodeRow)
open HeterogeneousSignedMatrixLowStrips (branches branchesCode)
open OriginalMatrixLowDimensionCode (RawHitRows rawDimension rawSupportSet)

def DecreasingLowCase (f : Nat → Nat) (B : Nat) (θ : Nat → Nat) (known : List Nat) (gates : List Gate)
    (p : NormalForm.Formula) (prior : (Nat → Nat) → Prop) (polarity : Bool) : Prop :=
  let source := matrix known gates p
  let bound := originalFamilyCeiling B known gates p
  ∃ name ∈ names known gates p, θ name < bound ∧ ∃ branch residual,
    branch ∈ branches f name bound source ∧ branch.1 = θ name ∧ HitRows branch.2 residual ∧
    supportSet residual = (supportSet source).erase name ∧ dimension residual < dimension source ∧
    prior θ ∧ ∃ suffix : Snapshot,
      actualRows f θ residual (passingList θ (circuit known gates p) ++ suffix) ∧
      OriginalPlainTerminalMatrix.accepts p polarity suffix

def ExactOriginalDecreasingLowCase : Prop :=
  ∀ (f : Nat → Nat) (B : Nat) (θ : Nat → Nat) (known : List Nat) (gates : List Gate)
    (p : NormalForm.Formula) (prior : (Nat → Nat) → Prop) (polarity : Bool),
      LowCase f B θ known gates p prior polarity ↔
        DecreasingLowCase f B θ known gates p prior polarity

def ExactOriginalCodedLowChildren : Prop :=
  ∀ (f : Nat → Nat) (B : Nat) (known : List Nat) (gates : List Gate) (p : NormalForm.Formula),
    ∀ name ∈ names known gates p,
      let source := (matrix known gates p).map encodeRow
      let bound := originalFamilyCeiling B known gates p
      ∀ branch ∈ branchesCode f (name,bound,source), ∀ residual : List RawRow,
        RawHitRows branch.2 residual →
          rawSupportSet residual = (rawSupportSet source).erase name ∧
          rawDimension residual < rawDimension source

/-- Same source, prior and positive graph, now with certified strict
dimension loss on the exact chosen low residual. High and empty unchanged. -/
def ExactOriginalDecreasingInitialPartition : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (θ : Nat → Nat) (known : List Nat) (gates : List Gate) (p : NormalForm.Formula),
    PreparedProjection.PlainPreparedFormula p →
    ∀ (prior : (Nat → Nat) → Prop) (polarity : Bool),
      (prior θ ∧ SourceAccepts f θ known gates p polarity) ↔
        DecreasingLowCase f B θ known gates p prior polarity ∨
          HighCase f B θ known gates p prior polarity ∨ ZeroCoordinateCase f θ known gates p prior polarity

def FullOriginalPrintedPlainMatrixDecreasingLow : Prop :=
  ExactOriginalDecreasingLowCase ∧ ExactOriginalCodedLowChildren ∧ ExactOriginalDecreasingInitialPartition

end LogicLineages.PermittedControl.OriginalPrintedPlainMatrixDecreasingLow
