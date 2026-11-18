module
public import LogicLineages.OrdinalComparison.CollectedRangeBandDefinitions
public import LogicLineages.OrdinalComparison.CollectedClosureBoundsDefinitions
public import LogicLineages.OrdinalComparison.SignedCollectedDifferenceDefinitions
public import Mathlib.Computability.Primrec.List

@[expose] public section
namespace LogicLineages.StandardControlCurrent.CellsTargets
open OrdinalComparison

def ActualOmegaHeadFormula : Prop :=
  ∀ n : Nat, actualProfileHead profileOmegaNote n=Phi (n+2)+1

def CollectedRangeThresholdCode : Prop :=
  Primrec encodedCollectedRangeThreshold ∧ ∀ A : CollectedPositiveNF,
    encodedCollectedRangeThreshold (collectedPositiveEncode A)=collectedRangeThreshold A

def CollectedNonlinearRangeBand : Prop :=
  ∀ (c b : Nat) (tags : CollectedPositiveTags), CollectedTagsValid tags → tags≠.nil →
    ∀ x : Nat, collectedRangeThreshold (.mk c b tags)≤x →
      let E := actualCollectedPositiveEval (.mk c b tags) x
      let Y := actualCollectedMaximumPeak tags x
      ∃ s : Nat, Y=Phi s ∧ Y<E ∧ E<Phi (s+1) ∧ E<actualProfileHead profileOmegaNote Y

def CollectedRangeCellTests : Prop :=
  ∀ (c b : Nat) (tags : CollectedPositiveTags), CollectedTagsValid tags → tags≠.nil →
    ∀ x : Nat, collectedRangeThreshold (.mk c b tags)≤x →
      ∀ V : Nat, V∈Set.range Phi →
        let E := actualCollectedPositiveEval (.mk c b tags) x
        (V<E ↔ ∃ (rho : NONote) (A : CollectedPositiveNF) (a : Nat),
          (rho,A,a)∈collectedTagEntries tags ∧ V≤actualCollectedTagPeak rho A x) ∧
        (E<V ↔ ∀ (rho : NONote) (A : CollectedPositiveNF) (a : Nat),
          (rho,A,a)∈collectedTagEntries tags → actualCollectedTagPeak rho A x<V) ∧ E≠V

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


/-- Complete current18 u:lem:cells, including actual effective tails. -/
def Full : Prop := ActualOmegaHeadFormula ∧ CollectedRangeThresholdCode ∧
  CollectedNonlinearRangeBand ∧ CollectedRangeCellTests ∧ ActualCollectedSignedCells
end LogicLineages.StandardControlCurrent.CellsTargets
