import LogicLineages.PersistentMarking.MarkedConstructorOperatorTargets
import LogicLineages.PersistentMarking.DecisionSourceBasicProof

namespace LogicLineages.PersistentMarking.MarkedConstructorInventoryProof
open Spine TypeSupport FiniteDomainFoundation
open MarkedConstructorOperator

theorem prefixSubtypes (σ : Ty) (ds : List Ty) (τ : Ty) (h : (ds,τ) ∈ fullPrefixes σ) :
    τ ∈ subtypes σ ∧ ∀ ρ, ρ ∈ ds → ρ ∈ subtypes σ := by
  induction σ generalizing ds τ with
  | ground => cases h
  | arrow α β ihα ihβ =>
    rcases List.mem_cons.mp h with h | h
    · cases h
      refine ⟨List.mem_cons_of_mem _ (List.mem_append_right _ (DecisionSourceBasicProof.subtypeSelf β)),?_⟩
      intro ρ hρ
      have he : ρ = α := by simpa using hρ
      subst ρ
      exact List.mem_cons_of_mem _ (List.mem_append_left _ (DecisionSourceBasicProof.subtypeSelf α))
    · obtain ⟨⟨ds',τ'⟩,hp,he⟩ := List.mem_map.mp h
      cases he
      obtain ⟨hτ,hds⟩ := ihβ ds' τ' hp
      refine ⟨List.mem_cons_of_mem _ (List.mem_append_right _ hτ),?_⟩
      intro ρ hρ
      rcases List.mem_cons.mp hρ with rfl | hρ
      · exact List.mem_cons_of_mem _ (List.mem_append_left _ (DecisionSourceBasicProof.subtypeSelf α))
      · exact List.mem_cons_of_mem _ (List.mem_append_right _ (hds ρ hρ))

theorem prefixClosed (s t : Expr) (σ τ : Ty)
    (hs : Typed EmptyContext s σ) (ht : Typed EmptyContext t τ)
    (hos : Ordinary s) (hot : Ordinary t) :
    MarkedConstructorTargets.PrefixClosed (environment s t) := by
  have hc := (DecisionSourceBasicProof.initial s t σ τ hs ht hos hot).1
  intro ρ hρ ds υ hpre
  obtain ⟨hυ,hds⟩ := prefixSubtypes ρ ds υ hpre
  exact ⟨hc ρ hρ υ hυ, fun α hα => hc ρ hρ α (hds α hα)⟩

end LogicLineages.PersistentMarking.MarkedConstructorInventoryProof
