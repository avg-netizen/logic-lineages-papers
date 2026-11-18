import LogicLineages.PersistentMarking.MarkedExtrasDownProof
import LogicLineages.PersistentMarking.HereditaryValueEqualityProof
import LogicLineages.PersistentMarking.HereditaryRestrictionProof
import LogicLineages.PersistentMarking.HereditaryCodeOrderProof
namespace LogicLineages.PersistentMarking.MarkedExtrasRestrictionProof
open Spine NameBridge DecisionPorts FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics HereditaryOrderTargets MarkedExtras

theorem codeMonotone (E : Environment) (σ : Ty) (Γ Θ : Context)
    (hw : WellFormed E.types E.ports Γ) (ht : WellFormed E.types E.ports Θ) (he : Extends Γ Θ)
    (a b : Code) (ha : a ∈ (descriptor E σ).carriers Γ) (hb : b ∈ (descriptor E σ).carriers Γ)
    (hab : (descriptor E σ).le Γ a b = true) :
    (descriptor E σ).le Θ ((descriptor E σ).restrict Γ Θ a) ((descriptor E σ).restrict Γ Θ b) = true := by
  have har := HereditaryRestrictionProof.restriction E σ Γ Θ hw ht he a ha
  have hbr := HereditaryRestrictionProof.restriction E σ Γ Θ hw ht he b hb
  apply (HereditaryCodeOrderProof.exactOrder E σ Θ _ _ ht har.1 hbr.1).mpr
  have hs := (HereditaryCodeOrderProof.exactOrder E σ Γ a b hw ha hb).mp hab
  apply HereditaryValueEqualityProof.order (HereditaryValueEqualityProof.symm har.2)
    (HereditaryValueEqualityProof.symm hbr.2)
  intro Δ hd hΘΔ
  exact hs Δ hd (DecisionPortsProof.extensionTrans Γ Θ Δ he hΘΔ)

theorem monotone : MarkedExtrasTargets.RestrictionMonotone := by
  intro E Γ Θ hw ht he
  constructor
  · rintro ⟨σ,a⟩ ha
    obtain ⟨hσ,ha⟩ := (MarkedExtrasFoundationProof.universeExact E Γ σ a).mp ha
    exact (MarkedExtrasFoundationProof.universeExact E Θ σ _).mpr
      ⟨hσ,(HereditaryRestrictionProof.restriction E σ Γ Θ hw ht he a ha).1⟩
  · rintro ⟨σ,a⟩ ⟨τ,b⟩ ha hb hab
    obtain ⟨hst,hab⟩ := (MarkedExtrasFoundationProof.orderExact E Γ σ τ a b).mp hab
    subst τ
    apply (MarkedExtrasFoundationProof.orderExact E Θ σ σ _ _).mpr
    exact ⟨rfl,codeMonotone E σ Γ Θ hw ht he a b
      ((MarkedExtrasFoundationProof.universeExact E Γ σ a).mp ha).2
      ((MarkedExtrasFoundationProof.universeExact E Γ σ b).mp hb).2 hab⟩

theorem weakening : MarkedExtrasTargets.Weakening := by
  intro E Γ Θ xs hw ht he hx
  apply MarkedExtrasDownProof.downExtra E Θ _ ht
  intro a ha; obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
  exact (monotone E Γ Θ hw ht he).1 b (MarkedExtrasDownProof.canonicalMember E Γ xs hx.1 b hb)
end LogicLineages.PersistentMarking.MarkedExtrasRestrictionProof
