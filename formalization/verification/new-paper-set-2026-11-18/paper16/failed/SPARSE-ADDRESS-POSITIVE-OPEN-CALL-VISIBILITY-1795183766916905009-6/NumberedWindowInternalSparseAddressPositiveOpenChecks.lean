module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveOpenForwardProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveOpenBackwardProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveOpenChecks
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalSparseAddressPositive
open NumberedWindowInternalSparseAddressPositiveOpenTargets
open NumberedWindowInternalSparseAddressPositiveOpenTapeProof (args)
open NumberedWindowInternalSparseAddressPositiveOpenForwardProof (forward)
open NumberedWindowInternalSparseAddressPositiveOpenBackwardProof (backward)

theorem exact_OpenAddressPositive : OpenAddressPositive := by
  intro body cv tv raw least α left cert right
  let a := programGraph (addressPositive cv tv raw least) (suc z) (args left cert right)
  let b := someAddressPositive cv tv raw least left cert right
  obtain ⟨f⟩ := forward (body := body) (Γ := [a]) cv tv raw least left cert right
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨r⟩ := backward (body := body) (Γ := [b]) cv tv raw least left cert right
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction f)
    (Derivation.implicationIntroduction r)⟩

#print axioms exact_OpenAddressPositive
end LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveOpenChecks
