module

public import LogicLineages.NativeModule.PersistentMarking.StructuralCoverageProof

@[expose] public section

namespace LogicLineages.PersistentMarking.StructuralStabilityProof
theorem fullStability : StructuralStabilityTargets.FullStability :=
  ⟨StructuralSubstitutionProof.weakSubstitution,StructuralSubstitutionProof.strictSubstitution,
    StructuralContextProof.weakContext,StructuralContextProof.strictContext⟩
end LogicLineages.PersistentMarking.StructuralStabilityProof
