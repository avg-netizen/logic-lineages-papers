import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchOriginalPositiveTargets
import LogicLineages.PersistentMarking.NumberedWindowArithmeticScalarChecks
import LogicLineages.PersistentMarking.NumberedWindowArithmeticAddressAlgorithmChecks
import LogicLineages.PersistentMarking.NumberedWindowArithmeticAllContextAdmittedProof
import LogicLineages.PersistentMarking.NumberedWindowArithmeticTyCodeProof

namespace LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchOriginalTypedAddressChecks
open NumberedWindowInternalFreshProbeDispatchOriginalPositiveTargets
open NumberedWindowTypedProbe (typed)
open NumberedWindowArithmeticClassAddress NumberedWindowArithmeticClassAddressProof
open NumberedWindowArithmeticScalarTargets (fixed)
open NumberedWindowArithmeticScalarChecks (exact_ScalarAddress)
open NumberedWindowArithmeticTyCode NumberedWindowAddressAlgorithm
open NumberedWindowArithmeticAddressAlgorithmTargets (address)
open NumberedWindowArithmeticAddressAlgorithmChecks (exact_ExactAddressView)

theorem originalView (a : ClassAddress) : addressView (encodeAddress a) = some (address a) := by
  rw [exact_ExactAddressView,round]
  rfl

/-- Classify every original raw typed input without importing any
raw application-decoder agreement. The converse also pays rejection. -/
theorem exact_OriginalTypedAddress : ExactOriginalTypedAddress := by
  intro S K hk τ n
  rw [typed,exact_ScalarAddress,Bool.and_eq_true]
  have had := NumberedWindowArithmeticAllContextAdmittedProof.admitted S K n hk
  constructor
  · rintro ⟨h,ht⟩
    obtain ⟨Γ,result,i,q,addr,hq⟩ := had.mp h
    rw [← addr,originalView] at ht
    have hty : encodeTy result = encodeTy τ := eq_of_beq ht
    have he := congrArg decodeTy hty
    simp only [NumberedWindowArithmeticTyCodeProof.roundtrip] at he
    cases Option.some.inj he
    exact ⟨Γ,i,q,addr.symm,hq⟩
  · rintro ⟨Γ,i,q,ha,hq⟩
    refine ⟨had.mpr ⟨Γ,τ,i,q,ha.symm,hq⟩,?_⟩
    rw [ha,originalView]
    change (encodeTy τ == encodeTy τ) = true
    simp

#print axioms exact_OriginalTypedAddress
end LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchOriginalTypedAddressChecks
