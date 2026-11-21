module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreForwardProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreReverseProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreOpenChecks
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparseApplicationOutputCore (outputCore)
open NumberedWindowInternalSparseApplicationOutputCoreTargets
open NumberedWindowInternalSparseApplicationOutputCoreEmitterProof (objectTape)
open NumberedWindowInternalSparseApplicationOutputCoreForwardProof (recover)
open NumberedWindowInternalSparseApplicationOutputCoreReverseProof (rebuild)

theorem exact_OpenApplicationOutputCore : ExactOpenApplicationOutputCore := by
  intro body least α Γ ctx dom cod fn arg y
  let selected := programGraph (outputCore least) (suc z) (objectTape ctx dom cod fn arg y)
  let report := outputReport least ctx cod (auxiliaryTerm dom cod fn arg) y
  obtain ⟨forward⟩ := recover (body := body) (Γ := selected :: Γ) least ctx dom cod fn arg y
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨backward⟩ := rebuild (body := body) (Γ := report :: Γ) least ctx dom cod fn arg y
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction forward)
    (Derivation.implicationIntroduction backward)⟩

#print axioms exact_OpenApplicationOutputCore
end LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreOpenChecks
