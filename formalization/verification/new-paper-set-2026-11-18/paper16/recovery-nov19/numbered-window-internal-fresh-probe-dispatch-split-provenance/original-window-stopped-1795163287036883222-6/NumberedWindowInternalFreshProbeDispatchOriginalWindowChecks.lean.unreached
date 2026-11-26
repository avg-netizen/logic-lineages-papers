import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchOriginalWindowTargets
import LogicLineages.PersistentMarking.NumberedWindowOriginalProbeTotalChecks
import LogicLineages.PersistentMarking.NumberedWindowArithmeticScalarChecks
import LogicLineages.PersistentMarking.NumberedWindowArithmeticAddressAlgorithmChecks
import LogicLineages.PersistentMarking.NumberedWindowTypingBitsChecks
import LogicLineages.PersistentMarking.NumberedWindowApplicationDomainProof

namespace LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchOriginalWindowChecks
open NumberedWindowInternalFreshProbeDispatchWindowTargets
open NumberedWindowInternalFreshProbeDispatchOriginalWindowTargets
open NumberedWindowTypedProbe (typed)
open NumberedWindowScalarAlgorithm (scalar)
open NumberedWindowArithmeticScalarTargets (fixed)
open NumberedWindowArithmeticAllContextBits (addressBit canonicalBit)
open NumberedWindowArithmeticClassAddress (decodeAddress)
open NumberedWindowArithmeticTermCode (decodeTerm)
open NumberedWindowArithmeticTyCode (encodeTy)
open NumberedWindowArithmeticAddressAlgorithmChecks (exact_ExactAddressView)
open NumberedWindowArithmeticAddressAlgorithmTargets (address)
open NumberedWindowArithmeticScalarChecks (exact_ScalarAddress)
open NumberedWindowOriginalComputabilityFormulaTargets (formulaType)
open NumberedWindowOriginalProbeTotalChecks (exact_FormulaTypeCoding exact_OriginalProbeTotal)
open NumberedWindowTypingBits (finiteWindowBit)
open NumberedWindowTypingBitsChecks (exact_FiniteWindowBit)
open NumberedWindowApplicationDomainProof (rootInWindow arrowRight subtypeSelf)
open NumberedWindowProbeCode (code)

theorem exact_OriginalTypeSupport : ExactOriginalTypeSupport := by
  intro S K t q ht
  change (scalar (fixed S K) q &&
    (NumberedWindowAddressAlgorithm.addressView q).any (fun a => a.2.1 == t)) = true at ht
  obtain ⟨hs,hv⟩ := Bool.and_eq_true.mp ht
  rw [exact_ScalarAddress S K] at hs
  rw [exact_ExactAddressView] at hv
  cases ha : decodeAddress q with
  | none => simp [addressBit,ha] at hs
  | some a =>
    have hc : canonicalBit S K a = true := by
      simpa only [addressBit,ha] using hs
    have hty : encodeTy a.result = t := by
      simpa [ha,address] using hv
    cases hq : decodeTerm a.least with
    | none => simp [canonicalBit,hq] at hc
    | some Q =>
      have hw : finiteWindowBit S K a.context a.result Q = true := by
        simp only [canonicalBit,hq,Bool.and_eq_true] at hc
        exact hc.1
      have hm := rootInWindow ((exact_FiniteWindowBit S K a.context a.result Q).mp hw)
      refine ⟨formulaType a.result,List.mem_map.mpr ⟨a.result,hm,rfl⟩,?_⟩
      exact hty.symm.trans (exact_FormulaTypeCoding a.result).symm

theorem exact_OriginalWindowChild : ExactOriginalWindowChild := by
  intro K hk σ τ h
  obtain ⟨ρ,hρ,he⟩ := List.mem_map.mp h
  cases ρ with
  | ground => cases he
  | arrow a b =>
    change LogicLineages.OrdinalComparison.Source.Ty.arrow (formulaType a) (formulaType b) =
      LogicLineages.OrdinalComparison.Source.Ty.arrow σ τ at he
    have hb : formulaType b = τ := (LogicLineages.OrdinalComparison.Source.Ty.arrow.inj he).2
    exact List.mem_map.mpr ⟨b,arrowRight hk hρ b (subtypeSelf b),hb⟩

theorem exact_OriginalValidWindow : ExactOriginalValidWindow := by
  intro S K hk
  exact ⟨exact_OriginalTypeSupport S K,exact_OriginalWindowChild K hk,exact_OriginalProbeTotal S K hk⟩

#print axioms exact_OriginalTypeSupport
#print axioms exact_OriginalWindowChild
#print axioms exact_OriginalValidWindow
end LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchOriginalWindowChecks
