module

public import LogicLineages.NativeModule.PersistentMarking.MarkedConstructorTargets
public import LogicLineages.NativeModule.PersistentMarking.StructuralMarkedActionProof
public import LogicLineages.NativeModule.PersistentMarking.MarkedFamilyOrderProof

@[expose] public section

namespace LogicLineages.PersistentMarking.MarkedConstructorLookupProof
open Spine DecisionPorts FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics
open MarkedFamilyParameters (Parameter)
open MarkedFamilyCoherence (InputLE)

theorem lookupMember (ps : List (Parameter × Nat)) (M : Code) (p : Parameter) (i : Nat)
    (h : MarkedFamilyCoding.lookup ps M p = some i) :
    ∃ b, (p,b) ∈ ps := by
  induction ps generalizing M with
  | nil => cases M <;> cases h
  | cons qb ps ih =>
    obtain ⟨q,b⟩ := qb
    cases M with
    | nil => cases h
    | cons j js =>
      by_cases he : MarkedFamilyParameters.parameterEq q p = true
      · have heq := (MarkedFamilyParameterProof.parameterEqExact q p).mp he
        subst q
        exact ⟨b,List.mem_cons_self⟩
      · obtain ⟨c,hc⟩ := ih js (by simpa only [MarkedFamilyCoding.lookup, if_neg he] using h)
        exact ⟨c,List.mem_cons_of_mem _ hc⟩

theorem actionValid (E : Environment) (heads : List Head) (M : Code) (p : Parameter) (a : Code)
    (h : StructuralActions.markedAction E heads M p = some a) :
    MarkedFamilyParameters.Valid E heads p ∧ a ∈ (descriptor E p.2.1).carriers p.2.2.1 := by
  change (MarkedFamilyCoding.lookup (MarkedFamilyParameters.schema E heads) M p).bind
    (fun i => ((descriptor E p.2.1).carriers p.2.2.1)[i]?) = some a at h
  cases hlookup : MarkedFamilyCoding.lookup (MarkedFamilyParameters.schema E heads) M p with
  | none => simp [hlookup] at h
  | some i =>
    have ha : ((descriptor E p.2.1).carriers p.2.2.1)[i]? = some a := by
      simpa only [hlookup,Option.bind_some] using h
    obtain ⟨b,hb⟩ := lookupMember _ M p i hlookup
    obtain ⟨q,hq,he⟩ := List.mem_map.mp hb
    have heq : q = p := congrArg Prod.fst he
    subst q
    exact ⟨(MarkedFamilyParameterProof.enumeration E heads p).mp hq,List.mem_of_getElem? ha⟩

theorem actionOrder (E : Environment) (heads : List Head) (M N : Code) (p : Parameter)
    (a : Code) (hm : M ∈ MarkedFamilyCoherence.retained E heads)
    (hn : N ∈ MarkedFamilyCoherence.retained E heads)
    (hmn : MarkedFamilyLattice.le E heads M N = true)
    (ha : StructuralActions.markedAction E heads M p = some a) :
    ∃ b, StructuralActions.markedAction E heads N p = some b ∧
      b ∈ (descriptor E p.2.1).carriers p.2.2.1 ∧ (descriptor E p.2.1).le p.2.2.1 a b = true := by
  have hp := (actionValid E heads M p a ha).1
  obtain ⟨b,hb,hcar⟩ := StructuralMarkedActionProof.sound E heads N p hn hp
  have hle := (MarkedFamilyOrderProof.orderExact E heads M N hm hn).mp hmn p hp
  rw [StructuralMarkedActionProof.decoded E heads M p a ha,
    StructuralMarkedActionProof.decoded E heads N p b hb] at hle
  exact ⟨b,hb,hcar,hle⟩

theorem actionInputOrder (E : Environment) (heads : List Head) (M : Code) (p q : Parameter)
    (a : Code) (hm : M ∈ MarkedFamilyCoherence.retained E heads)
    (hq : MarkedFamilyParameters.Valid E heads q) (hpq : InputLE E p q)
    (ha : StructuralActions.markedAction E heads M p = some a) :
    ∃ b, StructuralActions.markedAction E heads M q = some b ∧
      b ∈ (descriptor E q.2.1).carriers q.2.2.1 ∧ (descriptor E p.2.1).le p.2.2.1 a b = true := by
  have hp := (actionValid E heads M p a ha).1
  obtain ⟨b,hb,hcar⟩ := StructuralMarkedActionProof.sound E heads M q hm hq
  exact ⟨b,hb,hcar,(StructuralMarkedActionProof.laws E heads M hm).1 p q a b hp hq hpq ha hb⟩

end LogicLineages.PersistentMarking.MarkedConstructorLookupProof
