import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchOriginalTypedAddressChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchCanonicalAppGraphChecks
import LogicLineages.PersistentMarking.NumberedWindowFreeAddressChecks
import LogicLineages.PersistentMarking.NumberedWindowPathWitnessClassCode

namespace LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchOriginalFreshProof
open NumberedWindowInternalFreshProbeDispatchOriginalPositiveTargets
open NumberedWindowInternalFreshProbeDispatchOriginalTypedAddressChecks
open NumberedWindowInternalFreshProbeDispatchCanonicalAppGraphChecks (exact_CanonicalLiteralApplicationGraph)
open NumberedWindowTypedProbe (typed probe)
open NumberedWindowAddressApplication (arrowView graph)
open NumberedWindowArithmeticScalarTargets (fixed)
open NumberedWindowFreeAddress (freeAddress freshName)
open NumberedWindowArithmeticClassAddress (encodeAddress)
open NumberedWindowArithmeticAddressAlgorithmTargets (address)
open NumberedWindowArithmeticTyCode NumberedWindowArithmeticTermCode
open NumberedWindowArithmeticCodecLaws
open NumberedWindowSimulationData NumberedWindowPathWitnessTargets
open NumberedWindowFreeAddressChecks (exact_FreshArrowProbe)

theorem fresh : ExactOriginalFreshApplication := by
  intro S K hk σ τ n h
  obtain ⟨Γ,i,q,addr,hq⟩ := (exact_OriginalTypedAddress S K hk (.arrow σ τ) n).mp h
  obtain ⟨_,_,_,_,free⟩ := exact_FreshArrowProbe S K Γ hk σ τ q i hq
  have witness := free
  obtain ⟨U,_,hCodeU,hU,_,_⟩ := witness
  let u := freeAddress (Γ.map encodeTy) (encodeTy σ) (freshName i)
  let vClass := NumberedWindowExternalApplication.appClass hk q (classOf U)
  obtain ⟨k,hv⟩ := NumberedWindowPathWitnessClassCode.existsCode S K Γ τ hk vClass
  let v := encodeAddress ⟨Γ,τ,k⟩
  refine ⟨Γ,i,q,u,v,addr,hq,rfl,free,?_,?_,
    (exact_OriginalTypedAddress S K hk τ v).mpr ⟨Γ,k,vClass,rfl,hv⟩⟩
  · simp only [typed,Bool.and_eq_true] at h
    have allowed := h.1
    have arrow : arrowView (encodeTy (.arrow σ τ)) = some (encodeTy σ,encodeTy τ) := by
      simp [encodeTy,arrowView,← NumberedWindowActualPairAlgorithmChecks.currentDecoder,pairRound]
    rw [probe,allowed,addr]
    simp [originalView,address,arrow,u]
  · change graph (fixed S K) n (freeAddress (Γ.map encodeTy) (encodeTy σ) (freshName i)) v = true
    rw [addr,hCodeU]
    exact (exact_CanonicalLiteralApplicationGraph S K Γ σ τ hk q (classOf U)
      i (encodeTerm U.val) hq hU v).mpr ⟨k,rfl,hv⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchOriginalFreshProof
