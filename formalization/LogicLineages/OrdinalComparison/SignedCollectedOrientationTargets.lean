module
public import LogicLineages.OrdinalComparison.SparseSignedCollectedDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

def SignedCollectedPeakOrientation : Prop :=
  ∀ (row : SignedCollectedRow) (p q : Int) (x : Nat), SignedCollectedValid row → row≠[] →
    row.Pairwise (fun a b => actualCollectedTagPeak a.1.1 a.1.2 x≠
      actualCollectedTagPeak b.1.1 b.1.2 x) →
    signedCollectedRowBound row p q≤x →
    ∀ entry∈row,
      (∀ other∈row, actualCollectedTagPeak other.1.1 other.1.2 x≤
        actualCollectedTagPeak entry.1.1 entry.1.2 x) →
      Int.sign (actualSignedCollectedValue row x+p*(x : Int)+q)=Int.sign entry.2

end LogicLineages.OrdinalComparison.Targets
