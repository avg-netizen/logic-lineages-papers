import LogicLineages.PersistentMarking.NumberedWindowAddressApplicationTargets
import LogicLineages.PersistentMarking.NumberedWindowArithmeticAllContextAdmittedProof
import LogicLineages.PersistentMarking.NumberedWindowArithmeticLeastClassChecks

namespace LogicLineages.PersistentMarking.NumberedWindowAddressApplicationClassProof
open NumberedWindowAddressApplicationTargets NumberedWindowArithmeticClassAddress
open NumberedWindowArithmeticClassAddressProof (round)
open NumberedWindowArithmeticAllContextAdmittedProof (canonical)
open NumberedWindowArithmeticLeastClass NumberedWindowArithmeticLeastClassChecks
open NumberedWindowSimulationData NumberedWindowExternalApplication
open NumberedWindowArithmeticTermCode NumberedWindowPathWitnessTargets

private theorem leastRepresentative {S Γ τ K} (hk : DecisionSourceUniverse.Closed K)
    {x : Class S K (finiteC Γ) τ} {i : Nat} (h : ActualCodeAt S K Γ τ i x) :
    ∃ Q : WindowCarrier S K (finiteC Γ) τ, decodeTerm i = some Q.val ∧ classOf Q = x := by
  obtain ⟨R,hR,hi⟩ := h
  obtain ⟨k,Q,hk',hRep,he,hW,hP,_,_⟩ :=
    exact_LeastCodeSpecification S K Γ τ R.val hk R.property
  have ki : k = i := Option.some.inj (hk'.symm.trans hi)
  have hd := NumberedWindowArithmeticPathDecodeProof.termAt (he.trans ki)
  let C : WindowCarrier S K (finiteC Γ) τ := ⟨Q,hW⟩
  have eqClass : classOf R = classOf C := Quot.sound hP
  exact ⟨C,hd,eqClass.symm.trans hR⟩

theorem classExact : ExactClassApplication := by
  intro S K Γ σ τ hk q u i j hq hu value
  obtain ⟨Q,hQ,hQC⟩ := leastRepresentative hk hq
  obtain ⟨U,hU,hUC⟩ := leastRepresentative hk hu
  have qb := (canonical S K ⟨Γ,.arrow σ τ,i⟩ hk).mpr ⟨q,hq⟩
  have ub := (canonical S K ⟨Γ,σ,j⟩ hk).mpr ⟨u,hu⟩
  let A := appCarrier hk Q U
  have classEq : classOf A = appClass hk q u := by
    rw [← hQC,← hUC]
    rfl
  have valueAt (k : Nat) :
      leastCode S K Γ τ A.val = some k ↔ ActualCodeAt S K Γ τ k (appClass hk q u) := by
    constructor
    · exact fun h => ⟨A,classEq,h⟩
    · rintro ⟨B,hB,hkB⟩
      exact ((exact_LeastCodeReflectsActualQuotient S K Γ τ A B hk).mpr
        (classEq.trans hB.symm)).trans hkB
  simp only [decodedApplication,round,Option.bind_eq_bind,Option.bind_some,qb,ub,
    decide_true,Bool.true_and,if_true,hQ,hU]
  change (leastCode S K Γ τ A.val).map (fun k => encodeAddress ⟨Γ,τ,k⟩) = some value ↔ _
  rw [Option.map_eq_some_iff]
  constructor
  · rintro ⟨k,hkVal,he⟩
    exact ⟨k,he.symm,(valueAt k).mp hkVal⟩
  · rintro ⟨k,he,hkVal⟩
    exact ⟨k,(valueAt k).mpr hkVal,he.symm⟩

end LogicLineages.PersistentMarking.NumberedWindowAddressApplicationClassProof
