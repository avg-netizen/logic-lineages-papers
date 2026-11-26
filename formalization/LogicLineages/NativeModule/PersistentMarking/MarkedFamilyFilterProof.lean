module

public import LogicLineages.NativeModule.PersistentMarking.MarkedFamilyCoherenceFoundationProof
public import LogicLineages.NativeModule.PersistentMarking.MarkedFamilyRoundtripProof

@[expose] public section

namespace LogicLineages.PersistentMarking.MarkedFamilyFilterProof
open Spine NameBridge DecisionPorts FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode MarkedFamilyParameters MarkedFamilyCoding MarkedFamilyCoherence

theorem outputDecode (E : Environment) (heads : List Head) (c : Code) (p : Parameter)
    (hf : FitsFamily E heads c) (hp : MarkedFamilyParameters.Valid E heads p) :
    MarkedFamilyCoding.output E heads c p = some (MarkedFamilyCoding.decode E heads c p) := by
  obtain ⟨v,hv,_⟩ := MarkedFamilyLookupProof.outputSuccess E heads c p hf hp
  simp only [MarkedFamilyCoding.decode,hv,Option.getD_some]

theorem decodedValid (E : Environment) (heads : List Head) (c : Code) (hf : FitsFamily E heads c) :
    OutputsValid E heads (MarkedFamilyCoding.decode E heads c) := by
  intro p hp
  obtain ⟨v,hv,hm⟩ := MarkedFamilyLookupProof.outputSuccess E heads c p hf hp
  simpa only [MarkedFamilyCoding.decode,hv,Option.getD_some] using hm

theorem monotoneExact : MarkedFamilyCoherenceTargets.MonotoneExact := by
  intro E heads c hf
  unfold MarkedFamilyCoherence.monotoneBool
  simp only [List.all_eq_true]
  constructor
  · intro h p q hp hq hle
    have hm := h p ((MarkedFamilyParameterProof.enumeration E heads p).mpr hp)
      q ((MarkedFamilyParameterProof.enumeration E heads q).mpr hq)
    have hb := (MarkedFamilyCoherenceFoundationProof.inputOrderExact E heads p q hp hq).mpr hle
    simpa only [hb,if_true,outputDecode E heads c p hf hp,outputDecode E heads c q hf hq] using hm
  · intro h p hp q hq
    have hvp := (MarkedFamilyParameterProof.enumeration E heads p).mp hp
    have hvq := (MarkedFamilyParameterProof.enumeration E heads q).mp hq
    by_cases hb : MarkedFamilyCoherence.inputLe E p q = true
    · have hm := h p q hvp hvq ((MarkedFamilyCoherenceFoundationProof.inputOrderExact E heads p q hvp hvq).mp hb)
      simpa only [hb,if_true,outputDecode E heads c p hf hvp,outputDecode E heads c q hf hvq] using hm
    · simp only [if_neg hb]

theorem coherentExact : MarkedFamilyCoherenceTargets.CoherentExact := by
  intro E heads c hf
  unfold MarkedFamilyCoherence.coherentBool
  simp only [List.all_eq_true]
  constructor
  · intro h p hp Δ hw he
    have hd := MarkedFamilyCoherenceFoundationProof.destinationValid E heads p Δ hp hw he
    have hm := h p ((MarkedFamilyParameterProof.enumeration E heads p).mpr hp)
      Δ ((FiniteExtensionProof.enumeration E.types E.ports p.2.2.1 Δ).mpr ⟨hw,he⟩)
    simpa only [outputDecode E heads c p hf hp,outputDecode E heads c (weakenParameter E p Δ) hf hd,decide_eq_true_eq] using hm
  · intro h p hp Δ hΔ
    have hvp := (MarkedFamilyParameterProof.enumeration E heads p).mp hp
    obtain ⟨hw,he⟩ := (FiniteExtensionProof.enumeration E.types E.ports p.2.2.1 Δ).mp hΔ
    have hd := MarkedFamilyCoherenceFoundationProof.destinationValid E heads p Δ hvp hw he
    have hm := h p hvp Δ hw he
    simpa only [outputDecode E heads c p hf hvp,outputDecode E heads c (weakenParameter E p Δ) hf hd,decide_eq_true_eq] using hm
end LogicLineages.PersistentMarking.MarkedFamilyFilterProof
