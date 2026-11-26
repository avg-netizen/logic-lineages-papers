module
public import LogicLineages.PermittedControl.OriginalMatrixDenseRanksTargets
public import LogicLineages.PermittedControl.OriginalPrintedPlainMatrixInfiniteLowTargets

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedPlainMatrixDenseRanks
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open OriginalPrintedCircuitSequential (Gate)
open OriginalPrintedCircuitNormalization (Holds)
open OriginalPrintedPlainMatrixInfiniteLow (circuit matrix)
open OriginalNormalizedCircuitMatrix (passingList)
open OriginalMixedTerminalTest (Test)
open OriginalMatrixDenseRanks (support denseRows)
open ActualCoordinateRankChart (rankOf rankValue size)
open HeterogeneousSignedMatrixSlice (Snapshot actualRows)
open MixedSameRankResidue (WeightedOperand)

/-- The literal emitted prefix/suffix is ranked once from its entire
combined finite support. Original names in different rows never get
independent ranks or independent field inputs. -/
def ExactPrintedDenseRankedMatrix : Prop :=
  ∀ (f θ : Nat → Nat) (known : List Nat) (gates : List Gate)
    (p : NormalForm.Formula), PreparedProjection.PlainPreparedFormula p →
    ∀ positive : Bool,
      let original := matrix known gates p
      let names := support original
      let ρ := rankValue θ names
      let ranked := denseRows θ original
      let r := size θ names
      StrictMono ρ ∧
      (∀ i ∈ names, ∀ j ∈ names,
        (rankOf θ names i = rankOf θ names j ↔ θ i = θ j) ∧
        (rankOf θ names i < rankOf θ names j ↔ θ i < θ j)) ∧
      (∀ row ∈ ranked, ∀ t ∈ row.2.2, t.2.rank < r ∧ t.2.rank ≤ r - 1) ∧
      ((Holds f θ (circuit known gates p) ∧ (Test.rows p).atPolarity positive θ) ↔
        ∃ suffix : Snapshot,
          actualRows f ρ ranked (passingList θ (circuit known gates p) ++ suffix) ∧
          OriginalPlainTerminalMatrix.accepts p positive suffix)

end LogicLineages.PermittedControl.OriginalPrintedPlainMatrixDenseRanks
