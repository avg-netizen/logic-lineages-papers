module
public import LogicLineages.OrdinalComparison.SourceGammaCodedReductionSemanticProof
public import LogicLineages.OrdinalComparison.SourceMachineQueryCodeProgramsProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceGammaCodedReduction.Proof

theorem primitiveManyOneReduction : Targets.PrimitiveManyOneReduction := by
  intro b
  have hp : Primrec (SourceMachineQueryCode.output b) :=
    SourceMachineQueryCode.Proof.uniformPrimitiveRecursive.2.2.2.comp (Primrec.const b) Primrec.id
  have he : ∀ e,¬SourceBlankMachineSimulation.Halts e ↔
      Member (SourceMachineControlNonperiodicity.gamma b) (SourceMachineQueryCode.output b e) :=
    fun e => (exactNonhalting b e).symm
  exact ⟨hp,he,SourceMachineQueryCode.output b,hp.to_comp,he⟩
end LogicLineages.OrdinalComparison.Source.SourceGammaCodedReduction.Proof
