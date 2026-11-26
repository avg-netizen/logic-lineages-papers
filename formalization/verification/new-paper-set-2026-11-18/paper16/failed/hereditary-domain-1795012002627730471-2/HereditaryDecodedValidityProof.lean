import LogicLineages.PersistentMarking.HereditaryDecodedValiditySupport
namespace LogicLineages.PersistentMarking.HereditaryDecodedValidityProof
open Spine NameBridge DecisionPorts FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics HereditaryDecodedValiditySupport

theorem valid : HereditaryNaturalityBridgeTargets.DecodedValid := by
  intro E σ Γ c hΓ hc
  obtain ⟨hfits,hmono,hnatural⟩ := (HereditaryConstructionProof.effective E σ Γ c).mp hc
  refine ⟨?_,?_,?_⟩
  · intro Δ hw he ds τ hp vs ht
    exact HereditarySemanticOutputProof.decodeOutput E σ Γ Δ c ds τ hw he hc hp vs ht
  · intro Δ hw he ds τ hp vs ws hvs hws hle
    let p : Prefix σ := ⟨(ds,τ),hp⟩
    obtain ⟨xs,hxi,hxd,hxv⟩ := codeTuple E σ Δ p vs hvs
    obtain ⟨ys,hyi,hyd,hyv⟩ := codeTuple E σ Δ p ws hws
    obtain ⟨a,ha,ham⟩ := HereditaryOutputProof.outputExists E σ Γ Δ p xs c hw he hc hxv
    obtain ⟨b,hb,hbm⟩ := HereditaryOutputProof.outputExists E σ Γ Δ p ys c hw he hc hyv
    have hlex := (HereditaryTupleOrderProof.exactOrder E σ Δ p xs ys vs ws hxd hyd).mpr hle
    have hm := hmono
    unfold monotone at hm
    have hΔ := (FiniteExtensionProof.enumeration E.types E.ports Γ Δ).mpr ⟨hw,he⟩
    have hm1 := (List.all_eq_true.mp hm) Δ hΔ
    have hm2 := (List.all_eq_true.mp hm1) p (List.mem_attach _ _)
    have hm3 := (List.all_eq_true.mp hm2) xs hxv
    have hm4 := (List.all_eq_true.mp hm3) ys hyv
    rw [hlex] at hm4
    simp only [if_true,ha,hb] at hm4
    have hea := decodedOutput E σ Γ Δ p c xs vs a hxi ha
    have heb := decodedOutput E σ Γ Δ p c ys ws b hyi hb
    change (descriptor E τ).le Δ
      ((HereditaryDomainSemantics.decode E σ Γ c).application Δ p.val.1 p.val.2 vs)
      ((HereditaryDomainSemantics.decode E σ Γ c).application Δ p.val.1 p.val.2 ws) = true
    rw [hea,heb]
    exact hm4
  · intro Δ Θ hw hΘ he heΘ ds τ hp vs hvs
    let p : Prefix σ := ⟨(ds,τ),hp⟩
    obtain ⟨xs,hxi,hxd,hxv⟩ := codeTuple E σ Δ p vs hvs
    obtain ⟨a,ha,ham⟩ := HereditaryOutputProof.outputExists E σ Γ Δ p xs c hw he hc hxv
    have hn := hnatural
    unfold natural at hn
    have hΔ := (FiniteExtensionProof.enumeration E.types E.ports Γ Δ).mpr ⟨hw,he⟩
    have hΘmem := (FiniteExtensionProof.enumeration E.types E.ports Δ Θ).mpr ⟨hΘ,heΘ⟩
    have hn1 := (List.all_eq_true.mp hn) Δ hΔ
    have hn2 := (List.all_eq_true.mp hn1) Θ hΘmem
    have hn3 := (List.all_eq_true.mp hn2) p (List.mem_attach _ _)
    have hn4 := (List.all_eq_true.mp hn3) xs hxv
    cases hr : tupleRestrict σ (canonicalLower E σ) Δ Θ p xs with
    | none => simp [hr] at hn4
    | some ys =>
      cases hb : output E σ (canonicalLower E σ) Γ Θ p ys c with
      | none => simp [hr,ha,hb] at hn4
      | some b =>
        have hindex : indices E Θ p.val.1 (restrictValues E Δ Θ p.val.1 vs) = some ys := by
          rw [← HereditaryTupleRestrictionProof.exactRestriction E σ Δ Θ p xs vs hxd]
          exact hr
        have hea := decodedOutput E σ Γ Δ p c xs vs a hxi ha
        have heb := decodedOutput E σ Γ Θ p c ys (restrictValues E Δ Θ p.val.1 vs) b hindex hb
        have heq : (descriptor E τ).restrict Δ Θ a = b := by
          simpa [hr,ha,hb,resultDescriptor,canonicalLower] using hn4
        change (descriptor E τ).restrict Δ Θ
          ((HereditaryDomainSemantics.decode E σ Γ c).application Δ p.val.1 p.val.2 vs) =
          (HereditaryDomainSemantics.decode E σ Γ c).application Θ p.val.1 p.val.2 (restrictValues E Δ Θ p.val.1 vs)
        rw [hea,heb]
        exact heq

end LogicLineages.PersistentMarking.HereditaryDecodedValidityProof
