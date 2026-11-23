module

public import LogicLineages.NativeModule.PersistentMarking.HereditaryTupleProof
public import LogicLineages.NativeModule.PersistentMarking.HereditaryConstructionProof

@[expose] public section

namespace LogicLineages.PersistentMarking.HereditaryTupleRoundtripProof
open Spine NameBridge DecisionPorts FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics HereditaryTupleProof

/- The only distinctness used below is the checked actual global descriptor
carrier theorem, not a callback or an added premise. -/
theorem indicesAfterValues (E : Environment) (Δ : Context) (ds : List Ty) (is : List Nat) (vs : List Code)
    (h : HereditaryDomainSemantics.values E Δ ds is = some vs) :
    TupleValues E Δ ds vs ∧ indices E Δ ds vs = some is := by
  induction ds generalizing is vs with
  | nil =>
    cases is with
    | nil =>
      have he : vs = [] := (Option.some.inj h).symm
      subst vs; exact ⟨tupleNil E Δ,rfl⟩
    | cons i is => have hl := valuesLength E Δ [] (i::is) vs h; cases hl
  | cons ρ ds ih =>
    cases is with
    | nil => have hl := valuesLength E Δ (ρ::ds) [] vs h; cases hl
    | cons i is =>
      have hl := Nat.succ.inj (valuesLength E Δ (ρ::ds) (i::is) vs h)
      rw [valuesCons E Δ ρ ds i is hl] at h
      cases hi : ((descriptor E ρ).carriers Δ)[i]? with
      | none => simp [hi] at h
      | some v =>
        cases hvs : HereditaryDomainSemantics.values E Δ ds is with
        | none => simp [hi,hvs] at h
        | some ws =>
          have he : v::ws = vs := by simpa [hi,hvs] using h
          subst vs
          obtain ⟨ht,hr⟩ := ih is ws hvs
          have hm := List.mem_of_getElem? hi
          refine ⟨(tupleCons E Δ ρ ds v ws).mpr ⟨hm,ht⟩,?_⟩
          rw [indicesCons E Δ ρ ds v ws ht.1]
          rw [HereditaryLookupProof.indexAt _ v i (HereditaryConstructionProof.distinct E ρ Δ) hi,hr]
          rfl

end LogicLineages.PersistentMarking.HereditaryTupleRoundtripProof
