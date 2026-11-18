import LogicLineages.PersistentMarking.HereditaryLatticeTargets
import LogicLineages.PersistentMarking.FinitePrefixProof
namespace LogicLineages.PersistentMarking.HereditaryAggregateOrderProof
open Spine NameBridge DecisionPorts FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics HereditaryLatticeTargets HereditaryOrderTargets

theorem mappedMembers (E : Environment) (σ : Ty) (Γ Δ : Context) (xs : List Value)
    (hxs : ∀ v, v ∈ xs → Valid E σ Γ v) (hw : WellFormed E.types E.ports Δ) (he : Extends Γ Δ)
    (ds : List Ty) (τ : Ty) (hp : (ds,τ) ∈ fullPrefixes σ) (vs : List Code) (hv : TupleValues E Δ ds vs) :
    ∀ c, c ∈ xs.map (fun v => v.application Δ ds τ vs) → c ∈ (descriptor E τ).carriers Δ := by
  intro c hc; obtain ⟨v,hm,rfl⟩ := List.mem_map.mp hc
  exact (hxs v hm).1 Δ hw he ds τ hp vs hv

theorem order : AggregateOrder := by
  intro E σ Γ xs hΓ lower hxs
  refine ⟨?_,?_,?_,?_⟩
  · intro v hm Δ hw he
    refine ⟨?_,?_,?_⟩
    · intro h; exact List.any_eq_true.mpr ⟨v,hm,h⟩
    · intro t ht
      exact ⟨fun h => List.any_eq_true.mpr ⟨v,hm,h⟩,fun h => List.any_eq_true.mpr ⟨v,hm,h⟩⟩
    · intro ds τ hp vs hv
      exact ((lower τ (FinitePrefixProof.proper σ ds τ hp).1).1 Δ _ hw
        (mappedMembers E σ Γ Δ xs hxs hw he ds τ hp vs hv)).2.1 _ (List.mem_map.mpr ⟨v,hm,rfl⟩)
  · intro v hm Δ hw he
    refine ⟨?_,?_,?_⟩
    · intro h; exact List.all_eq_true.mp h v hm
    · intro t ht
      exact ⟨fun h => List.all_eq_true.mp h v hm,fun h => List.all_eq_true.mp h v hm⟩
    · intro ds τ hp vs hv
      exact ((lower τ (FinitePrefixProof.proper σ ds τ hp).1).2.1 Δ _ hw
        (mappedMembers E σ Γ Δ xs hxs hw he ds τ hp vs hv)).2.1 _ (List.mem_map.mpr ⟨v,hm,rfl⟩)
  · intro b hb hbound Δ hw he
    refine ⟨?_,?_,?_⟩
    · intro h
      obtain ⟨v,hm,hv⟩ := List.any_eq_true.mp h
      exact (hbound v hm Δ hw he).1 hv
    · intro t ht
      constructor
      · intro h; obtain ⟨v,hm,hv⟩ := List.any_eq_true.mp h
        exact ((hbound v hm Δ hw he).2.1 t ht).1 hv
      · intro h; obtain ⟨v,hm,hv⟩ := List.any_eq_true.mp h
        exact ((hbound v hm Δ hw he).2.1 t ht).2 hv
    · intro ds τ hp vs hv
      apply ((lower τ (FinitePrefixProof.proper σ ds τ hp).1).1 Δ _ hw
        (mappedMembers E σ Γ Δ xs hxs hw he ds τ hp vs hv)).2.2 _ (hb.1 Δ hw he ds τ hp vs hv)
      intro c hc; obtain ⟨v,hm,rfl⟩ := List.mem_map.mp hc
      exact (hbound v hm Δ hw he).2.2 ds τ hp vs hv
  · intro b hb hbound Δ hw he
    refine ⟨?_,?_,?_⟩
    · intro h
      apply List.all_eq_true.mpr
      intro v hm; exact (hbound v hm Δ hw he).1 h
    · intro t ht
      constructor
      · intro h; apply List.all_eq_true.mpr
        intro v hm; exact ((hbound v hm Δ hw he).2.1 t ht).1 h
      · intro h; apply List.all_eq_true.mpr
        intro v hm; exact ((hbound v hm Δ hw he).2.1 t ht).2 h
    · intro ds τ hp vs hv
      apply ((lower τ (FinitePrefixProof.proper σ ds τ hp).1).2.1 Δ _ hw
        (mappedMembers E σ Γ Δ xs hxs hw he ds τ hp vs hv)).2.2 _ (hb.1 Δ hw he ds τ hp vs hv)
      intro c hc; obtain ⟨v,hm,rfl⟩ := List.mem_map.mp hc
      exact (hbound v hm Δ hw he).2.2 ds τ hp vs hv
end LogicLineages.PersistentMarking.HereditaryAggregateOrderProof
