module
public import LogicLineages.OrdinalComparison.SourceGammaRestrictedReductionSyntaxProof
public import LogicLineages.OrdinalComparison.SourceGammaCodedReductionProof
public import LogicLineages.OrdinalComparison.SourceMachinePlanFragmentProof
public import LogicLineages.OrdinalComparison.SourceMachineInternalLevelProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceGammaRestrictedReduction.Proof

theorem generatedRange : Targets.GeneratedRange := by
  intro b e
  unfold SourceMachineQueryCode.output
  rw [(SourceMachineQueryCode.Proof.exactPackaging.2 b e).1]
  apply (exactSyntaxClass _ (SourceMachineRawValuations.Proof.groundContexts.2 b e) _ _).2
  have hf := SourceMachinePlanFragment.Proof.actualAggregateFragment b e
  have hl := SourceMachineInternalLevel.Proof.actualAggregateLevel b e
  exact ⟨hf.2.2,hf.2.1,hl.2,hl.1⟩

theorem restrictedManyOneReduction : Targets.RestrictedManyOneReduction := by
  intro b
  have hp := (SourceGammaCodedReduction.Proof.primitiveManyOneReduction b).1
  have he : ∀ e,¬SourceBlankMachineSimulation.Halts e ↔
      Member (SourceMachineControlNonperiodicity.gamma b) (SourceMachineQueryCode.output b e) := by
    intro e
    constructor
    · intro h
      exact ⟨generatedRange b e,(SourceGammaCodedReduction.Proof.exactNonhalting b e).2 h⟩
    · intro h
      exact (SourceGammaCodedReduction.Proof.exactNonhalting b e).1 h.2
  exact ⟨hp,he,SourceMachineQueryCode.output b,hp.to_comp,he⟩
end LogicLineages.OrdinalComparison.Source.SourceGammaRestrictedReduction.Proof
