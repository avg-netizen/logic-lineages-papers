module
public import LogicLineages.OrdinalComparison.ParametricCoefficientOneOrdinalProof
public import LogicLineages.OrdinalComparison.SourcePerturbedControlGrowthProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.ParametricCoefficientOne.Proof
open ParametricActualCollapse

theorem genericCoefficientOne : Targets.GenericCoefficientOne := by
  intro G hmono hmajor n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      change collapseWith G (Ordinal.omega0+(n : Ordinal)) = G (n+2)+1
      have ha := omega_tail_facts n
      apply Nat.le_antisymm
      · apply (ParametricActualCollapse.Proof.equation G _ ha.1).2
        intro x hx hnorm
        rcases predecessor_split n x hx with ⟨k,rfl⟩ | ⟨k,hk,rfl⟩
        · rw [(ParametricActualCollapse.Proof.natural_facts k).2,ha.2] at hnorm
          rw [ParametricActualCollapse.Proof.finiteValues G hmajor]
          omega
        · have hi := ih k hk
          change collapseWith G (Ordinal.omega0+(k : Ordinal)) = G (k+2)+1 at hi
          rw [hi]
          have hm := hmono (show k+2<n+2 by omega)
          omega
      · have hx : ((G (n+2) : Nat) : Ordinal) < Ordinal.omega0+(n : Ordinal) :=
          (Ordinal.natCast_lt_omega0 _).trans_le le_self_add
        have hn : actualOrdinalNorm ((G (n+2) : Nat) : Ordinal) ≤
            G (actualOrdinalNorm (Ordinal.omega0+(n : Ordinal))) := by
          rw [(ParametricActualCollapse.Proof.natural_facts _).2,ha.2]
        have hl := (ParametricActualCollapse.Proof.equation G _ ha.1).1 _ hx hn
        rw [ParametricActualCollapse.Proof.finiteValues G hmajor] at hl
        exact hl

theorem actualGammaCoefficientOne : Targets.ActualGammaCoefficientOne := by
  intro b
  have hm : StrictMono (SourceMachineControlNonperiodicity.gamma b) := by
    apply strictMono_nat_of_lt_succ
    intro n
    have h := PerturbedControl.Proof.growth b SourceBlankMachineSimulation.boundedH n
    change 4*SourceMachineControlNonperiodicity.gamma b n <
      SourceMachineControlNonperiodicity.gamma b (n+1) at h
    omega
  have hi : ∀ n : Nat, n ≤ SourceMachineControlNonperiodicity.gamma b n := by
    intro n
    have h := (PerturbedControl.Proof.bounds b SourceBlankMachineSimulation.boundedH n).1
    exact (self_lt_Phi n).le.trans h
  exact ⟨hm,hi,genericCoefficientOne _ hm hi⟩
end LogicLineages.OrdinalComparison.ParametricCoefficientOne.Proof
