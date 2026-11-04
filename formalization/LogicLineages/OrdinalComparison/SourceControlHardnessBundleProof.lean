module
public import LogicLineages.OrdinalComparison.SourceControlHardnessBundleTargets
public import LogicLineages.OrdinalComparison.SourceBlankMachineSimulationProof
public import LogicLineages.OrdinalComparison.SourceMachineControlNonperiodicityProof
public import LogicLineages.OrdinalComparison.SourceGammaCoREClassificationProof
public import LogicLineages.OrdinalComparison.SourceGammaWeakCoREClassificationProof
public import LogicLineages.OrdinalComparison.ParametricCanonicalObservationProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceControlHardnessBundle.Proof

theorem explicitEnumerationClock : Targets.ExplicitEnumerationClock := by
  have he := SourceBlankMachineSimulation.Proof.effectiveEnumeration
  exact ⟨he.1,he.2.1,he.2.2,SourceBlankMachineSimulation.Proof.exactTransitionClock,
    SourceBlankMachineSimulation.Proof.monotoneHalting.2,fun _ => rfl⟩

theorem fixedControlHardness : Targets.FixedControlHardness := by
  intro b
  exact ⟨(SourceMachineControlNonperiodicity.Proof.exactControlParity b).1,
    ⟨SourceGammaCoREClassification.Proof.reComplement b,
      SourceGammaCoREClassification.Proof.universalCoRE b⟩,
    ⟨SourceGammaWeakCoREClassification.Proof.reComplement b,
      SourceGammaWeakCoREClassification.Proof.universalCoRE b⟩,
    SourceMachineControlNonperiodicity.Proof.nonEventualPeriodicity b⟩

theorem canonicalObservation : Targets.CanonicalObservation := by
  intro b c hc Γ t ν hg hf
  have he := ParametricCanonicalObservation.Proof.scalarEquivalence
    (SourceMachineControlNonperiodicity.gamma b) c hc Γ t ν hg hf
  obtain ⟨n,hn⟩ := SourceRestrictedAssignmentFinite.Proof.finiteScalar
    (SourceMachineControlNonperiodicity.gamma b) Γ t ν hg hf
  exact ⟨⟨n,(he n).mpr hn⟩,he⟩
end LogicLineages.OrdinalComparison.Source.SourceControlHardnessBundle.Proof
