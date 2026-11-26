import LogicLineages.PersistentMarking.MarkedFamilyCodingTargets
import LogicLineages.PersistentMarking.MarkedFamilyParameterProof
namespace LogicLineages.PersistentMarking.MarkedFamilyEncodingProof
open Spine NameBridge DecisionPorts FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode MarkedFamilyParameters MarkedFamilyCoding

theorem traversalExact (ps : List Parameter) (car : Parameter → List Code) (v : Family) :
    (∀ p, p ∈ ps → v p ∈ car p) ↔ ∃ c,
    ps.mapM (fun p => HereditaryDomainCode.indexOf (car p) (v p)) = some c ∧
    Fits (ps.map (fun p => (car p).length)) c := by
  induction ps with
  | nil => simp [List.mapM_nil,Fits]
  | cons p ps ih =>
    constructor
    · intro h
      obtain ⟨i,hi⟩ := HereditaryLookupProof.indexExists (car p) (v p) (h p (by simp))
      have hb : i < (car p).length := (List.getElem?_eq_some_iff.mp (HereditaryLookupProof.indexSound _ _ _ hi)).1
      obtain ⟨cs,hcs,hf⟩ := ih.mp (fun q hq => h q (List.mem_cons_of_mem p hq))
      exact ⟨i::cs,by simp [List.mapM_cons,hi,hcs],⟨hb,hf⟩⟩
    · rintro ⟨c,hc,hf⟩
      cases hi : HereditaryDomainCode.indexOf (car p) (v p) with
      | none => simp [List.mapM_cons,hi] at hc
      | some i =>
        cases ht : ps.mapM (fun q => HereditaryDomainCode.indexOf (car q) (v q)) with
        | none => simp [List.mapM_cons,hi,ht] at hc
        | some cs =>
          have he : i::cs=c := by simpa [List.mapM_cons,hi,ht] using hc
          subst c
          have tail := ih.mpr ⟨cs,ht,hf.2⟩
          intro q hq
          rcases List.mem_cons.mp hq with hq|hq
          · subst q; exact List.mem_of_getElem? (HereditaryLookupProof.indexSound _ _ _ hi)
          · exact tail q hq

theorem encodingExact : MarkedFamilyCodingTargets.EncodingExact := by
  intro E heads v
  have h := traversalExact (parameters E heads)
    (fun p => (descriptor E p.2.1).carriers p.2.2.1) v
  constructor
  · intro hv
    obtain ⟨c,hc,hf⟩ := h.mp (fun p hp => hv p ((MarkedFamilyParameterProof.enumeration E heads p).mp hp))
    refine ⟨c,hc,?_⟩
    simpa only [FitsFamily,MarkedFamilyParameters.schema,List.map_map,Function.comp_def,MarkedFamilyParameters.bound] using hf
  · rintro ⟨c,hc,hf⟩
    have hfit : Fits ((parameters E heads).map (fun p => ((descriptor E p.2.1).carriers p.2.2.1).length)) c := by
      simpa only [FitsFamily,MarkedFamilyParameters.schema,List.map_map,Function.comp_def,MarkedFamilyParameters.bound] using hf
    intro p hp
    exact (h.mpr ⟨c,hc,hfit⟩) p ((MarkedFamilyParameterProof.enumeration E heads p).mpr hp)

theorem traversalCongruence (ps : List Parameter) (f g : Parameter → Option Nat)
    (h : ∀ p, p ∈ ps → f p=g p) : ps.mapM f = ps.mapM g := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    have hh := h p (by simp)
    have ht := ih (fun q hq => h q (List.mem_cons_of_mem p hq))
    simp only [List.mapM_cons,hh,ht]

theorem encodingCongruence : MarkedFamilyCodingTargets.EncodingCongruence := by
  intro E heads v w he
  apply traversalCongruence
  intro p hp
  rw [he p ((MarkedFamilyParameterProof.enumeration E heads p).mp hp)]
end LogicLineages.PersistentMarking.MarkedFamilyEncodingProof
