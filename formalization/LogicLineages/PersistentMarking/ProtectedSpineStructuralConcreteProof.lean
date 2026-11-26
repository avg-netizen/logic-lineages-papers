import LogicLineages.PersistentMarking.ProtectedSpineStructuralConcreteTargets
import LogicLineages.PersistentMarking.StructuralInterpretationCorrectedProof
import LogicLineages.PersistentMarking.ProtectedSpineFixedSimultaneousFreeAllCallProof
import LogicLineages.PersistentMarking.ProtectedSpineFixedMixedFrameCallProof
import LogicLineages.PersistentMarking.ProtectedSpineConcreteFreeCoverageProof

namespace LogicLineages.PersistentMarking.ProtectedSpineStructuralConcreteProof
open Spine ProtectedSpineStructuralConcreteTargets
open ProtectedSpineConcreteFreeCoverageProof
open ProtectedSpineFixedMixedFrameCallProof (exact_FixedMixedFrameCall)
open ProtectedSpineFixedSimultaneousFreeAllCallProof (exact_FixedSimultaneousFreeAllCall)

theorem exact_FixedConcreteWholeCall : FixedConcreteWholeCall := by
  intro S E H M Γ θ q xs τ a hc hm fix images typed cov callTy ix valid related
  exact exact_FixedSimultaneousFreeAllCall S E H M Γ θ q xs τ a hc hm fix images typed cov
    (exact_FreeSourceCoverage E H θ images q 0 cov) callTy ix
    (exact_FreeArgumentCoverage E H θ images xs 0 ix) valid related

theorem exact_FixedConcretePrefixCall : FixedConcretePrefixCall := by
  intro S E H M Γ θ q xs consumed types τ a hc hm fix images bound typed cov callTy ix valid related
  exact exact_FixedMixedFrameCall S E H M Γ θ q xs consumed types τ a hc hm fix images bound typed cov
    (exact_FreeSourceCoverage E H θ images q 0 cov) callTy ix
    (exact_FreeArgumentCoverage E H θ images xs 0 ix) valid related

/-- One gate for the prior structural conjunction and both newly
connected concrete-call scopes. -/
theorem exact_StructuralConcreteCore : StructuralConcreteCore :=
  ⟨StructuralInterpretationCorrected.correctedStructuralInterpretation,
    exact_FixedConcreteWholeCall,exact_FixedConcretePrefixCall⟩

#print axioms exact_FixedConcreteWholeCall
#print axioms exact_FixedConcretePrefixCall
#print axioms exact_StructuralConcreteCore
end LogicLineages.PersistentMarking.ProtectedSpineStructuralConcreteProof
