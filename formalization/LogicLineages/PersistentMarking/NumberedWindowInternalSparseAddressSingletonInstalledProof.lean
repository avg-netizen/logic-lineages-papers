module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressSingletonCoreProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveOpenBackwardProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveOpenBindingProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressSingletonInstalledProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus ID1Completion.SourcePresentation
open NumberedWindowInternalPresentationTargets (data)
open NumberedWindowInternalSparseAddressPositive (addressPositive)
open NumberedWindowInternalSparseAddressPositiveOpenTargets (witnessData)
open NumberedWindowInternalSparseAddressPositiveOpenBackwardProof (backward)
open NumberedWindowInternalSparseAddressPositiveOpenBindingProof (supply)
open NumberedWindowInternalSparseAddressSingletonTargets
open NumberedWindowInternalSparseAddressSingletonCoreProof (fromCalls)

theorem installed : ExactOpenInstalledSingleton := by
  intro i j cv tv d raw least c α left right ctx ty src dst q w r
  let R := addressPositive cv tv raw least
  let B := sourceBody (data i j R d) c
  let A := singletonInputs cv tv raw least left right ctx ty src dst q w r
  let cert := singletonCertificate dst q w r
  have h : Derivation B [A] A := Derivation.hypothesis List.mem_cons_self
  let others := Derivation.conjunctionRight h
  let tests := Derivation.conjunctionRight others
  let final := Derivation.conjunctionRight tests
  obtain ⟨path⟩ := fromCalls raw least ctx ty src dst q w r ⟨Derivation.conjunctionRight final⟩
  have row : Nonempty (Derivation B [A] (witnessData cv tv raw least left cert right ctx ty src dst)) :=
    ⟨Derivation.conjunctionIntroduction (Derivation.conjunctionLeft h)
      (Derivation.conjunctionIntroduction (Derivation.conjunctionLeft others)
        (Derivation.conjunctionIntroduction (Derivation.conjunctionLeft tests)
          (Derivation.conjunctionIntroduction (Derivation.conjunctionLeft final) path)))⟩
  obtain ⟨d⟩ := backward cv tv raw least left cert right
    (supply cv tv raw least left cert right ctx ty src dst row)
  exact ⟨Derivation.implicationIntroduction d⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressSingletonInstalledProof
