module

public import LogicLineages.NativeModule.PersistentMarking.MarkedFamilyEncodingProof
public import LogicLineages.NativeModule.PersistentMarking.MarkedFamilyLookupProof

@[expose] public section

namespace LogicLineages.PersistentMarking.MarkedFamilyRoundtripProof
open Spine NameBridge DecisionPorts FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode MarkedFamilyParameters MarkedFamilyCoding

theorem encodedLookup (ps : List Parameter) (b : Parameter → Nat) (f : Parameter → Option Nat)
    (c : Code) (hc : ps.mapM f = some c) (p : Parameter) (hp : p ∈ ps) :
    MarkedFamilyCoding.lookup (ps.map (fun q => (q,b q))) c p = f p := by
  induction ps generalizing c with
  | nil => cases hp
  | cons q qs ih =>
    cases hq : f q with
    | none => simp [List.mapM_cons,hq] at hc
    | some i =>
      cases ht : qs.mapM f with
      | none => simp [List.mapM_cons,hq,ht] at hc
      | some cs =>
        have he : i::cs=c := by simpa [List.mapM_cons,hq,ht] using hc
        subst c
        by_cases heq : parameterEq q p = true
        · have hqp := (MarkedFamilyParameterProof.parameterEqExact q p).mp heq
          subst q
          simpa only [List.map_cons,MarkedFamilyCoding.lookup,heq,if_true] using hq.symm
        · have hm : p ∈ qs := (List.mem_cons.mp hp).elim
            (fun h => False.elim (heq ((MarkedFamilyParameterProof.parameterEqExact q p).mpr h.symm))) id
          simp only [List.map_cons,MarkedFamilyCoding.lookup,if_neg heq]
          exact ih cs ht hm

theorem semanticRoundtrip : MarkedFamilyCodingTargets.SemanticRoundtrip := by
  intro E heads v c hv hc p hp
  have hm := (MarkedFamilyParameterProof.enumeration E heads p).mpr hp
  have hl := encodedLookup (parameters E heads) (MarkedFamilyParameters.bound E)
    (fun q => HereditaryDomainCode.indexOf ((descriptor E q.2.1).carriers q.2.2.1) (v q)) c hc p hm
  obtain ⟨i,hi⟩ := HereditaryLookupProof.indexExists _ _ (hv p hp)
  have hg := HereditaryLookupProof.indexSound _ _ _ hi
  simp only [MarkedFamilyCoding.decode,MarkedFamilyCoding.output,MarkedFamilyParameters.schema,hl,hi,Option.bind_some,hg,Option.getD_some]

theorem lookupAt (ps : List Parameter) (b : Parameter → Nat) (c : Code)
    (i : Nat) (p : Parameter) (v : Nat) (hd : ps.Pairwise (· ≠ ·))
    (hp : ps[i]? = some p) (hv : c[i]? = some v) :
    MarkedFamilyCoding.lookup (ps.map (fun q => (q,b q))) c p = some v := by
  induction ps generalizing c i with
  | nil => cases i <;> cases hp
  | cons q qs ih =>
    cases c with
    | nil => cases i <;> cases hv
    | cons x xs =>
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero,Option.some.injEq] at hp hv
        subst p; subst v
        simp only [List.map_cons,MarkedFamilyCoding.lookup,(MarkedFamilyParameterProof.parameterEqExact q q).mpr rfl,if_true]
      | succ i =>
        have hn := (List.pairwise_cons.mp hd).1 p (List.mem_of_getElem? hp)
        have he : ¬ parameterEq q p = true := fun h => hn ((MarkedFamilyParameterProof.parameterEqExact q p).mp h)
        simp only [List.map_cons,MarkedFamilyCoding.lookup,if_neg he]
        exact ih xs i (List.pairwise_cons.mp hd).2 hp hv

theorem rebuild (ps : List Parameter) (c : Code) (f : Parameter → Option Nat)
    (hl : ps.length=c.length)
    (h : ∀ (i : Nat) (p : Parameter) (v : Nat), ps[i]? = some p → c[i]? = some v → f p=some v) :
    ps.mapM f=some c := by
  induction ps generalizing c with
  | nil => cases c with
    | nil => rfl
    | cons v vs => cases hl
  | cons p ps ih => cases c with
    | nil => cases hl
    | cons v vs =>
      have hh := h 0 p v rfl rfl
      have ht := ih vs (Nat.succ.inj hl) (fun i q w hq hw => h (i+1) q w hq hw)
      simp [List.mapM_cons,hh,ht]

theorem codeRoundtrip : MarkedFamilyCodingTargets.CodeRoundtrip := by
  intro E heads c hf
  have hfit : Fits ((parameters E heads).map (MarkedFamilyParameters.bound E)) c := by
    simpa only [FitsFamily,MarkedFamilyParameters.schema,List.map_map,Function.comp_def] using hf
  obtain ⟨hlen,hbounds⟩ := (FiniteVectorProof.coordinates _ _).mp hfit
  apply rebuild
  · simpa only [List.length_map] using hlen
  · intro i p v hp hv
    have hb : ((parameters E heads).map (MarkedFamilyParameters.bound E))[i]? = some (MarkedFamilyParameters.bound E p) := by
      simp only [List.getElem?_map,hp,Option.map_some]
    have hbound := hbounds i (MarkedFamilyParameters.bound E p) v hb hv
    have hl := lookupAt (parameters E heads) (MarkedFamilyParameters.bound E) c i p v
      (MarkedFamilyParameterProof.distinct E heads) hp hv
    let value := ((descriptor E p.2.1).carriers p.2.2.1)[v]'hbound
    have hget : ((descriptor E p.2.1).carriers p.2.2.1)[v]? = some value := List.getElem?_eq_getElem hbound
    have hi := HereditaryLookupProof.indexAt _ value v (HereditaryConstructionProof.distinct E p.2.1 p.2.2.1) hget
    simpa only [MarkedFamilyCoding.decode,MarkedFamilyCoding.output,MarkedFamilyParameters.schema,hl,Option.bind_some,hget,Option.getD_some] using hi
end LogicLineages.PersistentMarking.MarkedFamilyRoundtripProof
