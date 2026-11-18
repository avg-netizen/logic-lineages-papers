import LogicLineages.PersistentMarking.MarkedExtrasTargets
import LogicLineages.PersistentMarking.FiniteEqualityProof
import LogicLineages.PersistentMarking.HereditaryPartialOrderProof
namespace LogicLineages.PersistentMarking.MarkedExtrasFoundationProof
open Spine NameBridge DecisionPorts FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode MarkedExtras

theorem universeExact : MarkedExtrasTargets.UniverseExact := by
  intro E Γ σ c
  unfold universe
  rw [FiniteEqualityProof.dedupMem _ (fun a b => by simp)]
  constructor
  · intro h
    obtain ⟨τ,ht,hm⟩ := List.mem_flatMap.mp h
    obtain ⟨v,hv,he⟩ := List.mem_map.mp hm
    cases he
    exact ⟨ht,hv⟩
  · rintro ⟨ht,hc⟩
    exact List.mem_flatMap.mpr ⟨σ,ht,List.mem_map.mpr ⟨c,hc,rfl⟩⟩

theorem distinct : MarkedExtrasTargets.UniverseDistinct := by
  intro E Γ
  exact FiniteEqualityProof.dedupDistinct _ (fun a b => by simp) _

theorem orderExact (E : Environment) (Γ : Context) (σ τ : Ty) (a b : Code) :
    le E Γ (σ,a) (τ,b) = true ↔ σ=τ ∧ (descriptor E σ).le Γ a b = true := by
  simp only [le,Bool.and_eq_true,decide_eq_true_eq]

theorem order : MarkedExtrasTargets.TaggedOrder := by
  intro E Γ hw
  refine ⟨?_,?_,?_⟩
  · rintro ⟨σ,a⟩ ha
    apply (orderExact E Γ σ σ a a).mpr
    exact ⟨rfl,(HereditaryPartialOrderProof.partialOrder E σ Γ hw).1 a ((universeExact E Γ σ a).mp ha).2⟩
  · rintro ⟨σ,a⟩ ⟨τ,b⟩ ⟨υ,c⟩ ha hb hc hab hbc
    obtain ⟨hστ,hab⟩ := (orderExact E Γ σ τ a b).mp hab
    obtain ⟨hτυ,hbc⟩ := (orderExact E Γ τ υ b c).mp hbc
    subst τ; subst υ
    exact (orderExact E Γ σ σ a c).mpr ⟨rfl,
      (HereditaryPartialOrderProof.partialOrder E σ Γ hw).2.1 a b c
        ((universeExact E Γ σ a).mp ha).2 ((universeExact E Γ σ b).mp hb).2
        ((universeExact E Γ σ c).mp hc).2 hab hbc⟩
  · rintro ⟨σ,a⟩ ⟨τ,b⟩ ha hb hab hba
    obtain ⟨he,hab⟩ := (orderExact E Γ σ τ a b).mp hab
    subst τ
    have hba := ((orderExact E Γ σ σ b a).mp hba).2
    have hab := (HereditaryPartialOrderProof.partialOrder E σ Γ hw).2.2 a b
      ((universeExact E Γ σ a).mp ha).2 ((universeExact E Γ σ b).mp hb).2 hab hba
    cases hab; rfl

theorem downExact : MarkedExtrasTargets.DownExact := by
  intro E Γ xs b
  simp only [down,List.mem_filter,List.any_eq_true]
end LogicLineages.PersistentMarking.MarkedExtrasFoundationProof
