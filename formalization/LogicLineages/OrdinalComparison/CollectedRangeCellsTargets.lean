module
public import LogicLineages.OrdinalComparison.CollectedRangeBandDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

def CollectedRangeCellTests : Prop :=
  ∀ (c b : Nat) (tags : CollectedPositiveTags), CollectedTagsValid tags → tags≠.nil →
    ∀ x : Nat, collectedRangeThreshold (.mk c b tags)≤x →
      ∀ V : Nat, V∈Set.range Phi →
        let E := actualCollectedPositiveEval (.mk c b tags) x
        (V<E ↔ ∃ (rho : NONote) (A : CollectedPositiveNF) (a : Nat),
          (rho,A,a)∈collectedTagEntries tags ∧ V≤actualCollectedTagPeak rho A x) ∧
        (E<V ↔ ∀ (rho : NONote) (A : CollectedPositiveNF) (a : Nat),
          (rho,A,a)∈collectedTagEntries tags → actualCollectedTagPeak rho A x<V) ∧ E≠V

end LogicLineages.OrdinalComparison.Targets
