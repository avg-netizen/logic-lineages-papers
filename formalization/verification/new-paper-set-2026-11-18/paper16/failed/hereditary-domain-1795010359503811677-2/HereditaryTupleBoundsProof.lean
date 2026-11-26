import LogicLineages.PersistentMarking.HereditaryTupleRoundtripProof
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

end LogicLineages.PersistentMarking.HereditaryTupleBoundsProof
