module
public import LogicLineages.OrdinalComparison.SparseSignedCollectedDefinitions
public import LogicLineages.OrdinalComparison.CollectedClosureBoundsDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

def SignedCollectedCoefficientBudget : Prop :=
  ∀ left right : CollectedPositiveTags,
    ((signedCollectedDifference left right).map (fun entry => entry.2.natAbs)).sum≤
      collectedCoefficientSum left+collectedCoefficientSum right

def SignedCollectedPairBudget : Prop :=
  ∀ (A B : CollectedPositiveNF) (M : Nat), collectedPositiveEncode A≤M → collectedPositiveEncode B≤M →
    let row := signedCollectedNFRow A B
    signedCollectedRowBound row.2.2 row.2.1 row.1≤max 4 (8*M+1) ∧
    row.1.natAbs+1≤max 4 (8*M+1)

def SignedCollectedRowIdentity : Prop :=
  ∀ A B : CollectedPositiveNF,
    let row := signedCollectedNFRow A B
    (row.1=0 ∧ row.2.1=0 ∧ row.2.2=[]) ↔ A=B

def SignedAffineTailNonzero : Prop :=
  ∀ (p q : Int) (x : Nat), p≠0 → q.natAbs+1≤x → p*(x : Int)+q≠0

end LogicLineages.OrdinalComparison.Targets
