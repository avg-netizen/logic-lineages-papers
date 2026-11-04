module
public import LogicLineages.OrdinalComparison.SourceControlNonperiodicitySimulationProof
public import LogicLineages.OrdinalComparison.SourcePerturbedControlComputabilityProof
public import LogicLineages.OrdinalComparison.CounterLeaderExpansionSuppliersProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.SourceControlNonperiodicity.Proof
attribute [local irreducible] Phi fastControl

theorem gamma_primitive (b : Nat) : Primrec (gamma b) :=
  PerturbedControl.Proof.control_primitive b boundedH bounded_primitive

theorem parity_exact (b n : Nat) (hn : b < n) :
    gamma b n % 2 = if boundedH (PerturbedControl.valuationTwo n,n) then 1 else 0 := by
  have he := Nat.even_iff.mp (CounterLeaderExpansion.Proof.phiEven n)
  have hz : n ≠ 0 := by omega
  unfold gamma PerturbedControl.control PerturbedControl.error
  simp only [if_neg hz,if_neg (by omega : ¬n ≤ b)]
  cases boundedH (PerturbedControl.valuationTwo n,n) <;> simp [Nat.add_mod,he]

theorem exactControlParity : Targets.ExactControlParity :=
  fun b => ⟨gamma_primitive b,parity_exact b⟩
end LogicLineages.OrdinalComparison.SourceControlNonperiodicity.Proof
