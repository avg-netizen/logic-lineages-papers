module

public import LogicLineages.NativeModule.PersistentMarking.HereditaryTupleRoundtripProof

@[expose] public section

namespace LogicLineages.PersistentMarking.HereditaryTupleBoundsProof
open Spine NameBridge DecisionPorts FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics HereditaryTupleProof

theorem decodeFits (E : Environment) (Δ : Context) (ds : List Ty) (is : List Nat)
    (h : Fits (ds.map (fun ρ => ((descriptor E ρ).carriers Δ).length)) is) :
    ∃ vs, HereditaryDomainSemantics.values E Δ ds is = some vs := by
  induction ds generalizing is with
  | nil =>
    cases is with
    | nil => exact ⟨[],rfl⟩
    | cons i is => cases h
  | cons ρ ds ih =>
    cases is with
    | nil => cases h
    | cons i is =>
      obtain ⟨vs,hvs⟩ := ih is h.2
      have hl := valuesLength E Δ ds is vs hvs
      let v := ((descriptor E ρ).carriers Δ)[i]'h.1
      have hv : ((descriptor E ρ).carriers Δ)[i]? = some v :=
        List.getElem?_eq_some_iff.mpr ⟨h.1,rfl⟩
      exact ⟨v::vs,by rw [valuesCons E Δ ρ ds i is hl,hv,hvs]; rfl⟩

theorem fitsDecode (E : Environment) (Δ : Context) (ds : List Ty) (is : List Nat) (vs : List Code)
    (h : HereditaryDomainSemantics.values E Δ ds is = some vs) :
    Fits (ds.map (fun ρ => ((descriptor E ρ).carriers Δ).length)) is := by
  induction ds generalizing is vs with
  | nil =>
    cases is with
    | nil => trivial
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
          exact ⟨(List.getElem?_eq_some_iff.mp hi).1,ih is ws hvs⟩

end LogicLineages.PersistentMarking.HereditaryTupleBoundsProof
