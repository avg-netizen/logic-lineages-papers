module
public import LogicLineages.OrdinalComparison.SparseSignedNumericalTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

def SparseSignedNumericalOrientation : Prop :=
  ∀ (row : List (Int × Nat × Nat)) (p q : Int) (x : Nat), row≠[] →
    (∀ entry∈row, entry.1≠0 ∧ x≤entry.2.2 ∧
      Phi entry.2.2<entry.2.1 ∧ entry.2.1<2*Phi entry.2.2) →
    row.Pairwise (fun a b => a.2.2≠b.2.2) →
    max 4 (2*(row.map (fun entry => entry.1.natAbs)).sum+p.natAbs+q.natAbs)≤x →
    ∀ entry∈row, (∀ other∈row, other.2.2≤entry.2.2) →
      Int.sign ((row.map (fun a => a.1*(a.2.1 : Int))).sum+p*(x : Int)+q)=Int.sign entry.1

end LogicLineages.OrdinalComparison.Targets
