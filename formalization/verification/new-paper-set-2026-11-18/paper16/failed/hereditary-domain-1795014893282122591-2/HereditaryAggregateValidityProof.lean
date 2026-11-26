import LogicLineages.PersistentMarking.HereditaryLatticeTargets
import LogicLineages.PersistentMarking.HereditaryPartialOrderProof
namespace LogicLineages.PersistentMarking.HereditaryAggregateValidityProof
open Spine NameBridge DecisionPorts FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics HereditaryLatticeTargets

theorem monotoneMap (E : Environment) (τ : Ty) (Δ : Context) (hw : WellFormed E.types E.ports Δ)
    (hj : JoinAt E τ) (hm : MeetAt E τ) (meet : Bool) (xs : List Value) (f g : Value → Code)
    (hf : ∀ v, v ∈ xs → f v ∈ (descriptor E τ).carriers Δ)
    (hg : ∀ v, v ∈ xs → g v ∈ (descriptor E τ).carriers Δ)
    (hle : ∀ v, v ∈ xs → (descriptor E τ).le Δ (f v) (g v) = true) :
    (descriptor E τ).le Δ
      (if meet then (descriptor E τ).meet Δ (xs.map f) else (descriptor E τ).join Δ (xs.map f))
      (if meet then (descriptor E τ).meet Δ (xs.map g) else (descriptor E τ).join Δ (xs.map g)) = true := by
  have hfm : ∀ c, c ∈ xs.map f → c ∈ (descriptor E τ).carriers Δ := by
    intro c hc; obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hc; exact hf v hv
  have hgm : ∀ c, c ∈ xs.map g → c ∈ (descriptor E τ).carriers Δ := by
    intro c hc; obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hc; exact hg v hv
  have ht := (HereditaryPartialOrderProof.partialOrder E τ Δ hw).2.1
  cases meet with
  | false =>
    have hleft := hj Δ (xs.map f) hw hfm
    have hright := hj Δ (xs.map g) hw hgm
    apply hleft.2.2 _ hright.1
    intro c hc; obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hc
    exact ht _ _ _ (hf v hv) (hg v hv) hright.1 (hle v hv)
      (hright.2.1 _ (List.mem_map.mpr ⟨v,hv,rfl⟩))
  | true =>
    have hleft := hm Δ (xs.map f) hw hfm
    have hright := hm Δ (xs.map g) hw hgm
    apply hright.2.2 _ hleft.1
    intro c hc; obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hc
    exact ht _ _ _ hleft.1 (hf v hv) (hg v hv)
      (hleft.2.1 _ (List.mem_map.mpr ⟨v,hv,rfl⟩)) (hle v hv)

theorem valid : AggregateValid := by
  intro E σ Γ meet xs hΓ lower hxs
  refine ⟨?_,?_,?_⟩
  · intro Δ hw he ds τ hp vs hv
    have hl := lower τ (FinitePrefixProof.proper σ ds τ hp).1
    have hm : ∀ c, c ∈ xs.map (fun v => v.application Δ ds τ vs) → c ∈ (descriptor E τ).carriers Δ := by
      intro c hc; obtain ⟨v,hv',rfl⟩ := List.mem_map.mp hc
      exact (hxs v hv').1 Δ hw he ds τ hp vs hv
    cases meet with
    | false => exact (hl.1 Δ _ hw hm).1
    | true => exact (hl.2.1 Δ _ hw hm).1
  · intro Δ hw he ds τ hp vs ws hv hws hle
    have hl := lower τ (FinitePrefixProof.proper σ ds τ hp).1
    exact monotoneMap E τ Δ hw hl.1 hl.2.1 meet xs _ _
      (fun v hm => (hxs v hm).1 Δ hw he ds τ hp vs hv)
      (fun v hm => (hxs v hm).1 Δ hw he ds τ hp ws hws)
      (fun v hm => (hxs v hm).2.1 Δ hw he ds τ hp vs ws hv hws hle)
  · intro Δ Θ hd ht he heΘ ds τ hp vs hv
    have hl := lower τ (FinitePrefixProof.proper σ ds τ hp).1
    have hm : ∀ c, c ∈ xs.map (fun v => v.application Δ ds τ vs) → c ∈ (descriptor E τ).carriers Δ := by
      intro c hc; obtain ⟨v,hv',rfl⟩ := List.mem_map.mp hc
      exact (hxs v hv').1 Δ hd he ds τ hp vs hv
    have hr := hl.2.2 Δ Θ _ hd ht heΘ hm
    have heq : (xs.map (fun v => v.application Δ ds τ vs)).map ((descriptor E τ).restrict Δ Θ) =
        xs.map (fun v => v.application Θ ds τ (restrictValues E Δ Θ ds vs)) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro v hm
      exact (hxs v hm).2.2 Δ Θ hd ht he heΘ ds τ hp vs hv
    cases meet with
    | false => simpa only [aggregate,Bool.false_eq_true,if_false,heq] using hr.1
    | true => simpa only [aggregate,if_true,heq] using hr.2
end LogicLineages.PersistentMarking.HereditaryAggregateValidityProof
