module

public import LogicLineages.NativeModule.PersistentMarking.MarkedConstructorHeadExactProof
public import LogicLineages.NativeModule.PersistentMarking.MarkedConstructorTestChecks
public import LogicLineages.NativeModule.PersistentMarking.MarkedConstructorSelectOrderProof
public import LogicLineages.NativeModule.PersistentMarking.MarkedConstructorStatOrderProof

@[expose] public section

namespace LogicLineages.PersistentMarking.MarkedConstructorWeakOrderProof
open Spine DecisionPorts FiniteDomainSchema HereditaryDomainCode
open MarkedFamilyParameters (Parameter)
open MarkedConstructorTargets
open MarkedConstructorOwnerOrderProof (OwnerOrder)

theorem weakOrder (S : Signature) (E : Environment) (heads : List Head) (M N : Code)
    (p q : Parameter) (t : Expr)
    (hp : MarkedFamilyParameters.Valid E heads p) (hq : MarkedFamilyParameters.Valid E heads q)
    (hf : p.1 = q.1) (hτ : p.2.1 = q.2.1) (hΓ : p.2.2.1 = q.2.2.1)
    (howner : OwnerOrder E heads M N p q)
    (htag : ∀ a, a ∈ MarkedConstructorSelectOrderProof.selectedTags p →
      ∃ b, b ∈ MarkedConstructorSelectOrderProof.selectedTags q ∧ MarkedExtras.le E p.2.2.1 a b = true)
    (hreplace : ∀ ts, Replaces E p.2.2.1 (p.1.arguments.zip p.2.2.2.1) ts →
      Replaces E q.2.2.1 (q.1.arguments.zip q.2.2.2.1) ts)
    (hfabs : FAbsWitness E heads M p t → FAbsWitness E heads N q t)
    (h : MarkedConstructorTests.weakTest S E heads M p t = true) :
    MarkedConstructorTests.weakTest S E heads N q t = true := by
  simp only [MarkedConstructorTests.weakTest, Bool.or_eq_true] at h ⊢
  rcases h with ((h | h) | h) | h
  · have hw := (MarkedConstructorSelectProof.select E heads M p t).mp h
    have hw' := MarkedConstructorSelectOrderProof.selectOrder E heads M N p q hp hq hτ hΓ t howner htag hw
    exact Or.inl (Or.inl (Or.inl ((MarkedConstructorSelectProof.select E heads N q t).mpr hw')))
  · obtain ⟨g,ts,he,hr,hprec,hwhole⟩ := (MarkedConstructorHeadExactProof.copy S E heads M p t).mp h
    have hw := MarkedConstructorOwnerOrderProof.wholeOrder E heads M N p q hΓ hp.2.2.1 howner _ hwhole
    exact Or.inl (Or.inl (Or.inr ((MarkedConstructorHeadExactProof.copy S E heads N q t).mpr
      ⟨g,ts,he,hr.trans hτ,hf ▸ hprec,hw⟩)))
  · obtain ⟨g,ts,he,hr,hstat,hm,hwhole⟩ := (MarkedConstructorHeadExactProof.stat S E heads M p t).mp h
    have hw := MarkedConstructorOwnerOrderProof.wholeOrder E heads M N p q hΓ hp.2.2.1 howner _ hwhole
    exact Or.inl (Or.inr ((MarkedConstructorHeadExactProof.stat S E heads N q t).mpr
      ⟨g,ts,he,hr.trans hτ,hf ▸ hstat,hreplace _ hm,hw⟩))
  · exact Or.inr ((MarkedConstructorFAbsExactProof.fabs E heads N q t).mpr
      (hfabs ((MarkedConstructorFAbsExactProof.fabs E heads M p t).mp h)))

end LogicLineages.PersistentMarking.MarkedConstructorWeakOrderProof
