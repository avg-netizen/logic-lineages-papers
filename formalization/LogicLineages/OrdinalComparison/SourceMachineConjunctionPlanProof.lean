module
public import LogicLineages.OrdinalComparison.SourceMachineConjunctionPlanSemanticProof
public import LogicLineages.OrdinalComparison.SourceMachineConjunctionPlanSizeProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceMachineConjunctionPlan.Proof
open ExistentialPlan ParametricExistentialPlan

private theorem compiled_conjunction (b e : Nat) (ρ : Variable Base .ground → Nat) :
    (∃ ν : Variable (compile (plan b e)).context .ground → Nat,
      (∀ x,ν ((compile (plan b e)).embedding x)=ρ x) ∧
      HoldsWith (SourceMachineControlNonperiodicity.gamma b) (compile (plan b e)) ν) ↔
    SourceMachineHaltingConjunction.Conjunction b e
      (ρ (original 0)) (ρ (original 1)) (ρ (original 2)) (ρ (original 3)) := by
  rw [← ParametricExistentialPlan.Proof.actualGammaCompilation b Base (plan b e) (supportedSyntax b e) ρ]
  exact exactConjunction b e ρ

theorem exactCompiledHalting : Targets.ExactCompiledHalting := by
  refine ⟨compiled_conjunction,?_⟩
  intro b e
  constructor
  · rintro ⟨ν,hν⟩
    let ρ : Variable Base .ground → Nat := fun x => ν ((compile (plan b e)).embedding x)
    have hc := (compiled_conjunction b e ρ).mp ⟨ν,fun _ => rfl,hν⟩
    exact (SourceMachineHaltingConjunction.Proof.exactHaltingReduction b e).mp
      ⟨ρ (original 0),ρ (original 1),ρ (original 2),ρ (original 3),hc⟩
  · intro h
    obtain ⟨t,z,y,w,hc⟩ := (SourceMachineHaltingConjunction.Proof.exactHaltingReduction b e).mpr h
    let empty : Variable [] .ground → Nat := fun x => nomatch x
    let ρ : Variable Base .ground → Nat :=
      ExistentialPlan.extend (ExistentialPlan.extend (ExistentialPlan.extend
        (ExistentialPlan.extend empty w) y) z) t
    have hv : SourceMachineHaltingConjunction.Conjunction b e
        (ρ (original 0)) (ρ (original 1)) (ρ (original 2)) (ρ (original 3)) := hc
    obtain ⟨ν,_,hν⟩ := (compiled_conjunction b e ρ).mpr hv
    exact ⟨ν,hν⟩
end LogicLineages.OrdinalComparison.Source.SourceMachineConjunctionPlan.Proof
