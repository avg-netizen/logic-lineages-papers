import LogicLineages.PersistentMarking.HereditaryEncodingSupport
import LogicLineages.PersistentMarking.HereditaryTupleOrderProof
import LogicLineages.PersistentMarking.HereditaryTupleRestrictionProof
namespace LogicLineages.PersistentMarking.HereditaryEncodedRetentionProof
open Spine NameBridge DecisionPorts FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics HereditaryEncodingSupport

theorem retained : HereditaryEncodingTargets.EncodedRetained := by
  intro E σ Γ v hΓ hlower hvalid
  apply (HereditaryConstructionProof.effective E σ Γ (encode E σ Γ v)).mpr
  refine ⟨HereditaryEncodedFitsProof.fits E σ Γ v hvalid,?_,?_⟩
  · unfold monotone
    apply List.all_eq_true.mpr
    intro Δ hΔ
    obtain ⟨hw,he⟩ := (FiniteExtensionProof.enumeration E.types E.ports Γ Δ).mp hΔ
    apply List.all_eq_true.mpr
    intro p hp
    apply List.all_eq_true.mpr
    intro xs hx
    apply List.all_eq_true.mpr
    intro ys hy
    obtain ⟨vs,hvs⟩ := (HereditaryPrefixCodingProof.decodeExact E σ Δ p xs).mp hx
    obtain ⟨ws,hws⟩ := (HereditaryPrefixCodingProof.decodeExact E σ Δ p ys).mp hy
    have ha := encodedOutput E σ Γ Δ v p xs vs hvalid hw he hvs
    have hb := encodedOutput E σ Γ Δ v p ys ws hvalid hw he hws
    by_cases hle : tupleLe σ (canonicalLower E σ) Δ p xs ys = true
    · have hv := hvs
      have hw' := hws
      rw [HereditaryTupleAdapterProof.tupleDecodeCanonical] at hv hw'
      have htv := (HereditaryTupleRoundtripProof.indicesAfterValues E Δ p.val.1 xs vs hv).1
      have htw := (HereditaryTupleRoundtripProof.indicesAfterValues E Δ p.val.1 ys ws hw').1
      have hrel := (HereditaryTupleOrderProof.exactOrder E σ Δ p xs ys vs ws hvs hws).mp hle
      have hm := hvalid.2.1 Δ hw he p.val.1 p.val.2 p.property vs ws htv htw hrel
      simpa only [hle,if_true,ha,hb,resultDescriptor,canonicalLower] using hm
    · simp only [if_neg hle]
  · unfold natural
    apply List.all_eq_true.mpr
    intro Δ hΔ
    obtain ⟨hw,he⟩ := (FiniteExtensionProof.enumeration E.types E.ports Γ Δ).mp hΔ
    apply List.all_eq_true.mpr
    intro Θ hΘ
    obtain ⟨hwΘ,heΘ⟩ := (FiniteExtensionProof.enumeration E.types E.ports Δ Θ).mp hΘ
    apply List.all_eq_true.mpr
    intro p hp
    apply List.all_eq_true.mpr
    intro xs hx
    obtain ⟨vs,hvs⟩ := (HereditaryPrefixCodingProof.decodeExact E σ Δ p xs).mp hx
    have hv := hvs
    rw [HereditaryTupleAdapterProof.tupleDecodeCanonical] at hv
    have htv := (HereditaryTupleRoundtripProof.indicesAfterValues E Δ p.val.1 xs vs hv).1
    have hsmall := (FinitePrefixProof.proper σ p.val.1 p.val.2 p.property).2
    have htr := restrictedTuple E σ Δ Θ p.val.1 vs hsmall hlower hw hwΘ heΘ htv
    obtain ⟨ys,hys⟩ := HereditaryTupleProof.indicesExist E Θ p.val.1 (restrictValues E Δ Θ p.val.1 vs) htr
    have hr : tupleRestrict σ (canonicalLower E σ) Δ Θ p xs = some ys := by
      rw [HereditaryTupleRestrictionProof.exactRestriction E σ Δ Θ p xs vs hvs]
      exact hys
    have hdys : tupleDecode σ (canonicalLower E σ) Θ p ys = some (restrictValues E Δ Θ p.val.1 vs) := by
      rw [HereditaryTupleAdapterProof.tupleDecodeCanonical]
      exact (HereditaryTupleProof.valuesAfterIndices E Θ p.val.1 (restrictValues E Δ Θ p.val.1 vs) ys hys).2
    have ha := encodedOutput E σ Γ Δ v p xs vs hvalid hw he hvs
    have hb := encodedOutput E σ Γ Θ v p ys (restrictValues E Δ Θ p.val.1 vs) hvalid hwΘ
      (DecisionPortsProof.extensionTrans Γ Δ Θ he heΘ) hdys
    have hn := hvalid.2.2 Δ Θ hw hwΘ he heΘ p.val.1 p.val.2 p.property vs htv
    simpa only [hr,ha,hb,resultDescriptor,canonicalLower,decide_eq_true_eq] using hn

end LogicLineages.PersistentMarking.HereditaryEncodedRetentionProof
