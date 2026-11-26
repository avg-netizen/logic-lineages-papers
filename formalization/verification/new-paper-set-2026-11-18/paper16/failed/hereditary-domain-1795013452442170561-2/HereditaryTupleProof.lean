import LogicLineages.PersistentMarking.HereditaryLookupProof
namespace LogicLineages.PersistentMarking.HereditaryTupleProof
open Spine NameBridge DecisionPorts FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics

theorem indicesNil (E : Environment) (Δ : Context) : indices E Δ [] [] = some [] := rfl

theorem valuesNil (E : Environment) (Δ : Context) : HereditaryDomainSemantics.values E Δ [] [] = some [] := rfl

theorem indicesCons (E : Environment) (Δ : Context) (ρ : Ty) (ds : List Ty) (v : Code) (vs : List Code)
    (hlen : ds.length = vs.length) :
    indices E Δ (ρ::ds) (v::vs) = (do
      let i ← indexOf ((descriptor E ρ).carriers Δ) v
      let is ← indices E Δ ds vs
      pure (i::is)) := by
  simp [indices,hlen,List.mapM_cons]

theorem valuesCons (E : Environment) (Δ : Context) (ρ : Ty) (ds : List Ty) (i : Nat) (is : List Nat)
    (hlen : ds.length = is.length) :
    HereditaryDomainSemantics.values E Δ (ρ::ds) (i::is) = (do
      let v ← ((descriptor E ρ).carriers Δ)[i]?
      let vs ← HereditaryDomainSemantics.values E Δ ds is
      pure (v::vs)) := by
  simp [HereditaryDomainSemantics.values,hlen,List.mapM_cons]

theorem indicesLength (E : Environment) (Δ : Context) (ds : List Ty) (vs : List Code) (is : List Nat)
    (h : indices E Δ ds vs = some is) : ds.length = vs.length := by
  unfold indices at h
  split at h
  · assumption
  · cases h

theorem valuesLength (E : Environment) (Δ : Context) (ds : List Ty) (is : List Nat) (vs : List Code)
    (h : HereditaryDomainSemantics.values E Δ ds is = some vs) : ds.length = is.length := by
  unfold HereditaryDomainSemantics.values at h
  split at h
  · assumption
  · cases h

/- Both directions are about actual simultaneously traversed coordinates.
No equal-index assumption is made across different contexts. -/
theorem tupleNil (E : Environment) (Δ : Context) : TupleValues E Δ [] [] := by
  constructor
  · rfl
  · intro i ρ v h; cases i <;> cases h

theorem tupleCons (E : Environment) (Δ : Context) (ρ : Ty) (ds : List Ty) (v : Code) (vs : List Code) :
    TupleValues E Δ (ρ::ds) (v::vs) ↔ v ∈ (descriptor E ρ).carriers Δ ∧ TupleValues E Δ ds vs := by
  constructor
  · intro h
    refine ⟨h.2 0 ρ v rfl rfl,?_,?_⟩
    · exact Nat.succ.inj h.1
    · intro i τ w hd hv
      exact h.2 (i+1) τ w hd hv
  · intro h
    constructor
    · exact congrArg Nat.succ h.2.1
    · intro i τ w hd hv
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero,Option.some.injEq] at hd hv
        cases hd; cases hv; exact h.1
      | succ i => exact h.2.2 i τ w hd hv
theorem indicesExist (E : Environment) (Δ : Context) (ds : List Ty) (vs : List Code)
    (h : TupleValues E Δ ds vs) : ∃ is, indices E Δ ds vs = some is := by
  induction ds generalizing vs with
  | nil =>
    cases vs with
    | nil => exact ⟨[],rfl⟩
    | cons v vs => cases h.1
  | cons ρ ds ih =>
    cases vs with
    | nil => cases h.1
    | cons v vs =>
      have ht := (tupleCons E Δ ρ ds v vs).mp h
      obtain ⟨i,hi⟩ := HereditaryLookupProof.indexExists _ v ht.1
      obtain ⟨is,his⟩ := ih vs ht.2
      exact ⟨i::is,by rw [indicesCons E Δ ρ ds v vs ht.2.1,hi,his]; rfl⟩

theorem valuesAfterIndices (E : Environment) (Δ : Context) (ds : List Ty) (vs : List Code) (is : List Nat)
    (h : indices E Δ ds vs = some is) :
    ds.length = is.length ∧ HereditaryDomainSemantics.values E Δ ds is = some vs := by
  induction ds generalizing vs is with
  | nil =>
    cases vs with
    | nil =>
      have he : is = [] := (Option.some.inj h).symm
      subst is; exact ⟨rfl,rfl⟩
    | cons v vs => have hl := indicesLength E Δ [] (v::vs) is h; cases hl
  | cons ρ ds ih =>
    cases vs with
    | nil => have hl := indicesLength E Δ (ρ::ds) [] is h; cases hl
    | cons v vs =>
      have hl := Nat.succ.inj (indicesLength E Δ (ρ::ds) (v::vs) is h)
      rw [indicesCons E Δ ρ ds v vs hl] at h
      cases hi : indexOf ((descriptor E ρ).carriers Δ) v with
      | none => simp [hi] at h
      | some i =>
        cases his : indices E Δ ds vs with
        | none => simp [hi,his] at h
        | some js =>
          have he : i::js = is := by simpa [hi,his] using h
          subst is
          obtain ⟨hlen,hr⟩ := ih vs js his
          refine ⟨congrArg Nat.succ hlen,?_⟩
          rw [valuesCons E Δ ρ ds i js hlen,HereditaryLookupProof.indexSound _ v i hi,hr]
          rfl

end LogicLineages.PersistentMarking.HereditaryTupleProof
