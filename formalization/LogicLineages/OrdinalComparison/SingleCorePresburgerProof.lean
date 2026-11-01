module
public import LogicLineages.OrdinalComparison.SingleCorePresburgerSemanticProof
public import LogicLineages.OrdinalComparison.SingleCorePresburgerProgramProof
public import LogicLineages.OrdinalComparison.SingleCorePresburgerVariablesProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.SingleCorePresburger

theorem output : Targets.ActualSingleCorePresburgerOutput := by
  intro d E row hE hrow desired hDesired
  refine ⟨compiledFormula (multivariatePositiveEncode E) (singleCoreRowCode row) desired,
    output_code _ _ _,?_,?_⟩
  · intro i hi
    have hm := compiled_variables (multivariatePositiveEncode E) (singleCoreRowCode row) desired i hi
    rwa [SingleCoreSupport.source E] at hm
  · exact fun ρ hρ => output_value d E row hE hrow desired ρ hρ

theorem full : Targets.FullActualSingleCorePresburger := ⟨programs,output,universal_correct⟩

end LogicLineages.OrdinalComparison.SingleCorePresburger
