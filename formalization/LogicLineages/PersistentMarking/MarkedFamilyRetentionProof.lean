import LogicLineages.PersistentMarking.MarkedFamilyFilterProof
namespace LogicLineages.PersistentMarking.MarkedFamilyRetentionProof
open Spine NameBridge DecisionPorts FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode MarkedFamilyParameters MarkedFamilyCoding MarkedFamilyCoherence

theorem retentionExact : MarkedFamilyCoherenceTargets.RetentionExact := by
  intro E heads c
  simp only [MarkedFamilyCoherence.retained,List.mem_filter,Bool.and_eq_true]
  constructor
  · rintro ⟨hc,hm,hn⟩
    have hf := (MarkedFamilyLookupProof.rawEnumeration E heads c).mp hc
    exact ⟨hf,MarkedFamilyFilterProof.decodedValid E heads c hf,
      (MarkedFamilyFilterProof.monotoneExact E heads c hf).mp hm,
      (MarkedFamilyFilterProof.coherentExact E heads c hf).mp hn⟩
  · rintro ⟨hf,hv,hm,hn⟩
    exact ⟨(MarkedFamilyLookupProof.rawEnumeration E heads c).mpr hf,
      (MarkedFamilyFilterProof.monotoneExact E heads c hf).mpr hm,
      (MarkedFamilyFilterProof.coherentExact E heads c hf).mpr hn⟩

theorem encodingComplete : MarkedFamilyCoherenceTargets.EncodingComplete := by
  intro E heads v hv
  obtain ⟨c,hc,hf⟩ := (MarkedFamilyEncodingProof.encodingExact E heads v).mp hv.1
  have he := MarkedFamilyRoundtripProof.semanticRoundtrip E heads v c hv.1 hc
  refine ⟨c,hc,(retentionExact E heads c).mpr ⟨hf,MarkedFamilyFilterProof.decodedValid E heads c hf,?_,?_⟩,he⟩
  · intro p q hp hq hle
    rw [he p hp,he q hq]
    exact hv.2.1 p q hp hq hle
  · intro p hp Δ hw hext
    have hd := MarkedFamilyCoherenceFoundationProof.destinationValid E heads p Δ hp hw hext
    rw [he p hp,he (weakenParameter E p Δ) hd]
    exact hv.2.2 p hp Δ hw hext
end LogicLineages.PersistentMarking.MarkedFamilyRetentionProof
