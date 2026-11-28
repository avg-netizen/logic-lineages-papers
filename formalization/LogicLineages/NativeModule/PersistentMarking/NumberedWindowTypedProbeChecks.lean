module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowTypedProbeTargets
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowFreeAddressChecks
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowApplicationGraphChecks
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticScalarChecks
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticAddressAlgorithmChecks
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticAllContextAdmittedProof
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowPathWitnessClassCode

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowTypedProbeChecks
open NumberedWindowTypedProbe NumberedWindowTypedProbeTargets NumberedWindowFreeAddress
open NumberedWindowArithmeticClassAddress NumberedWindowArithmeticClassAddressProof
open NumberedWindowArithmeticScalarTargets (fixed)
open NumberedWindowArithmeticScalarChecks (exact_ScalarAddress)
open NumberedWindowSimulationData NumberedWindowPathWitnessTargets NumberedWindowArithmeticLeastClass
open NumberedWindowArithmeticTyCode NumberedWindowAddressAlgorithm
open NumberedWindowArithmeticAddressAlgorithmTargets (address)
open NumberedWindowArithmeticAddressAlgorithmChecks (exact_ExactAddressView)
open NumberedWindowAddressApplication (arrowView graph)
open NumberedWindowArithmeticCodecLaws
private theorem view (a : ClassAddress) : addressView (encodeAddress a) = some (address a) := by
  rw [exact_ExactAddressView,round]
  rfl

theorem exact_TypedAddress : ExactTypedAddress := by
  intro S K hk τ n
  rw [typed,exact_ScalarAddress,Bool.and_eq_true]
  have admitted := NumberedWindowArithmeticAllContextAdmittedProof.admitted S K n hk
  constructor
  · rintro ⟨h,ty⟩
    obtain ⟨Γ,result,i,q,addr,hq⟩ := admitted.mp h
    rw [← addr,view] at ty
    have same : encodeTy result = encodeTy τ := eq_of_beq ty
    have eqType := congrArg decodeTy same
    simp only [NumberedWindowArithmeticTyCodeProof.roundtrip] at eqType
    cases Option.some.inj eqType
    exact ⟨Γ,i,q,addr.symm,hq⟩
  · rintro ⟨Γ,i,q,addr,hq⟩
    refine ⟨admitted.mpr ⟨Γ,τ,i,q,addr.symm,hq⟩,?_⟩
    rw [addr,view]
    change (encodeTy τ == encodeTy τ) = true
    simp

theorem exact_FreshProbeApplication : FreshProbeApplication := by
  intro S K hk σ τ n h
  obtain ⟨Γ,i,q,addr,hq⟩ := (exact_TypedAddress S K hk (.arrow σ τ) n).mp h
  obtain ⟨Q,_,_,_,free⟩ := NumberedWindowFreeAddressChecks.exact_FreshArrowProbe S K Γ hk σ τ q i hq
  have witness := free
  obtain ⟨U,_,code,hu,_,_⟩ := witness
  let u := freeAddress (Γ.map encodeTy) (encodeTy σ) (freshName i)
  let vClass := NumberedWindowExternalApplication.appClass hk q (classOf U)
  obtain ⟨k,hv⟩ := NumberedWindowPathWitnessClassCode.existsCode S K Γ τ hk vClass
  let v := encodeAddress ⟨Γ,τ,k⟩
  refine ⟨Γ,i,q,u,v,addr,hq,rfl,free,?_,?_,(exact_TypedAddress S K hk τ v).mpr ⟨Γ,k,vClass,rfl,hv⟩⟩
  · simp only [typed,Bool.and_eq_true] at h
    have allowed := h.1
    have arrow : arrowView (encodeTy (.arrow σ τ)) = some (encodeTy σ,encodeTy τ) := by
      simp [encodeTy,arrowView,← NumberedWindowActualPairAlgorithmChecks.currentDecoder,pairRound]
    rw [probe,allowed,addr]
    simp [view,address,arrow,u]
  · rw [addr]
    apply (NumberedWindowApplicationGraphChecks.exact_ClassApplicationGraph S K Γ σ τ hk q i hq u v).mpr
    exact ⟨_,classOf U,k,code,hu,rfl,hv⟩

#print axioms exact_TypedAddress
#print axioms exact_FreshProbeApplication
end LogicLineages.PersistentMarking.NumberedWindowTypedProbeChecks
