module
public import LogicLineages.OrdinalComparison.SourceMachineAggregateBridgePointwiseProof
public import LogicLineages.OrdinalComparison.SourceMachineConjunctionPlanProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceMachineAggregateBridge.Proof

theorem existentialEquality : Targets.ExistentialEquality := by
  intro b e
  exact (exists_congr (equal_iff_holds b e)).trans
    (SourceMachineConjunctionPlan.Proof.exactCompiledHalting.2 b e)

theorem universalStrictNonhalting : Targets.UniversalStrictNonhalting := by
  intro b e
  constructor
  · intro h hh
    obtain ⟨ρ,hρ⟩ := (SourceMachineConjunctionPlan.Proof.exactCompiledHalting.2 b e).mpr hh
    exact (strict_iff_not_holds b e ρ).mp (h ρ) hρ
  · intro hn ρ
    apply (strict_iff_not_holds b e ρ).mpr
    intro hρ
    exact hn ((SourceMachineConjunctionPlan.Proof.exactCompiledHalting.2 b e).mp ⟨ρ,hρ⟩)
end LogicLineages.OrdinalComparison.Source.SourceMachineAggregateBridge.Proof
