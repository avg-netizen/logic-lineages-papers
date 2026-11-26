module

public import LogicLineages.NativeModule.PersistentMarking.MarkedFamilyCodingTargets
public import LogicLineages.NativeModule.PersistentMarking.MarkedFamilyParameterProof

@[expose] public section

namespace LogicLineages.PersistentMarking.MarkedFamilyLookupProof
open Spine NameBridge DecisionPorts FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode MarkedFamilyParameters MarkedFamilyCoding

theorem rawEnumeration : MarkedFamilyCodingTargets.RawEnumeration := by
  intro E heads c
  exact FiniteVectorProof.exactVector _ _

theorem bounded (ps : List Parameter) (b : Parameter → Nat) (c : Code) (p : Parameter)
    (hf : Fits (ps.map b) c) (hp : p ∈ ps) : ∃ i,
    MarkedFamilyCoding.lookup (ps.map (fun q => (q,b q))) c p = some i ∧ i < b p := by
  induction ps generalizing c with
  | nil => cases hp
  | cons q qs ih =>
    cases c with
    | nil => cases hf
    | cons i is =>
      by_cases he : parameterEq q p = true
      · have hqp := (MarkedFamilyParameterProof.parameterEqExact q p).mp he
        subst q
        exact ⟨i,by simp only [List.map_cons,MarkedFamilyCoding.lookup,he,if_true],hf.1⟩
      · have htail : p ∈ qs := (List.mem_cons.mp hp).elim
          (fun h => False.elim (he ((MarkedFamilyParameterProof.parameterEqExact q p).mpr h.symm))) id
        obtain ⟨j,hj,hb⟩ := ih is hf.2 htail
        exact ⟨j,by simp only [List.map_cons,MarkedFamilyCoding.lookup,if_neg he]; exact hj,hb⟩

theorem coordinateSuccess : MarkedFamilyCodingTargets.CoordinateSuccess := by
  intro E heads c p hf hp
  have hm := (MarkedFamilyParameterProof.enumeration E heads p).mpr hp
  have hfit : Fits ((parameters E heads).map (MarkedFamilyParameters.bound E)) c := by
    simpa only [FitsFamily,MarkedFamilyParameters.schema,List.map_map,Function.comp_def] using hf
  exact bounded (parameters E heads) (MarkedFamilyParameters.bound E) c p hfit hm

theorem outputSuccess : MarkedFamilyCodingTargets.OutputSuccess := by
  intro E heads c p hf hp
  obtain ⟨i,hi,hb⟩ := coordinateSuccess E heads c p hf hp
  let v := ((descriptor E p.2.1).carriers p.2.2.1)[i]
  have hv : ((descriptor E p.2.1).carriers p.2.2.1)[i]? = some v := List.getElem?_eq_getElem hb
  exact ⟨v,by simp only [MarkedFamilyCoding.output,hi,Option.bind_some]; exact hv,List.mem_of_getElem? hv⟩
end LogicLineages.PersistentMarking.MarkedFamilyLookupProof
