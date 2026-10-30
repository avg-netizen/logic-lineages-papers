module
public import LogicLineages.OrdinalComparison.CollectedRangeBandTargets
public import LogicLineages.OrdinalComparison.CollectedRangeCellsTargets
public import LogicLineages.OrdinalComparison.CollectedClosureBoundsDefinitions
public import LogicLineages.OrdinalComparison.SignedCollectedDifferenceDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

/-- Pointwise coefficient orientation after actual finite-height separation.
The greatest peak is an attained finite maximum, never a supplied oracle. -/
def ActualCollectedSignedCells : Prop :=
  Primrec encodedCollectedZeroBound ∧
  ∀ forms : List CollectedPositiveNF, (∀ A∈forms, CollectedPositiveValid A) →
    let N := encodedCollectedZeroBound (forms.map collectedPositiveEncode)
    N=collectedFiniteZeroBound forms ∧ 1≤N ∧
    ∀ x : Nat, N≤x → ∀ A∈collectedFiniteClosure forms, ∀ B∈collectedFiniteClosure forms,
      let row := signedCollectedNFRow A B
      (row.2.2=[] → (actualCollectedPositiveEval A x : Int)-(actualCollectedPositiveEval B x : Int)=
        row.1+row.2.1*(x : Int)) ∧
      (row.2.2≠[] →
        (∃ entry∈row.2.2,
          (∀ other∈row.2.2, actualCollectedTagPeak other.1.1 other.1.2 x≤
            actualCollectedTagPeak entry.1.1 entry.1.2 x) ∧
          Int.sign ((actualCollectedPositiveEval A x : Int)-(actualCollectedPositiveEval B x : Int))=
            Int.sign entry.2) ∧
        ∀ entry∈row.2.2,
          (∀ other∈row.2.2, actualCollectedTagPeak other.1.1 other.1.2 x≤
            actualCollectedTagPeak entry.1.1 entry.1.2 x) →
          Int.sign ((actualCollectedPositiveEval A x : Int)-(actualCollectedPositiveEval B x : Int))=
            Int.sign entry.2)

/-- Entire source paper07 lem:cells, with actual effective range tests and
signed-row orientation, not the later two-sort eventual-sign algorithm. -/
def FullActualCollectedCells : Prop :=
  ActualOmegaHeadFormula ∧ CollectedRangeThresholdCode ∧ CollectedNonlinearRangeBand ∧
    CollectedRangeCellTests ∧ ActualCollectedSignedCells

end LogicLineages.OrdinalComparison.Targets
