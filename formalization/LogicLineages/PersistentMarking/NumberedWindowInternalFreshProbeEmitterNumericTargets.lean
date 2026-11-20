module
public import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeEmitterDefinitions
@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeEmitterNumericTargets
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowFieldAlgorithm (pack)
open NumberedWindowFreeAddress (freeAddress)
open NumberedWindowTypedProbe (probe)
open NumberedWindowInternalFreshProbeEmitter
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector

def ExactPackedFreeEmitterValue : Prop :=
  (∀ c t n, evaluate packedEmitter (c ::ᵥ t ::ᵥ n ::ᵥ nil) = packedFree c t n) ∧
  (∀ (Γ : List Nat) t n, evaluate packedEmitter (pack Γ ::ᵥ t ::ᵥ n ::ᵥ nil) = freeAddress Γ t n)

/-- The particular chosen conditional is an exact witness to the original
#608 option-code existential. This is not an object conversion theorem
for a different opaque witness with the same standard-natural values. -/
def ExactOriginalSelectedFreshEmitter : Prop :=
  ∀ s : Settings, ∃ p : Selectors,
    calibrated s p ∧
    ∀ q, evaluate (chooseFresh p) (q ::ᵥ nil) = Encodable.encode (probe s q)

end LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeEmitterNumericTargets
