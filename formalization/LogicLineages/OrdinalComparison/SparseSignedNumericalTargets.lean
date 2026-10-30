module
public import LogicLineages.OrdinalComparison.CollectedAffineBandDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

/-- Numerical supplier only: actual head-value and index calibration are
explicit local premises, to be discharged in the separate signed-row stage. -/
def SparseSignedNumericalNonzero : Prop :=
  ∀ (row : List (Int × Nat × Nat)) (p q : Int) (x : Nat), row≠[] →
    (∀ entry∈row, entry.1≠0 ∧ x≤entry.2.2 ∧
      Phi entry.2.2<entry.2.1 ∧ entry.2.1<2*Phi entry.2.2) →
    row.Pairwise (fun a b => a.2.2≠b.2.2) →
    max 4 (2*(row.map (fun entry => entry.1.natAbs)).sum+p.natAbs+q.natAbs)≤x →
    (row.map (fun entry => entry.1*(entry.2.1 : Int))).sum+p*(x : Int)+q≠0

def PhiPreviousProductGap : Prop :=
  ∀ s k : Nat, 0<s → k≤s → k*Phi (s-1)<Phi s

end LogicLineages.OrdinalComparison.Targets
