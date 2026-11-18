import LogicLineages.PersistentMarking.HereditaryLatticeTargets
import LogicLineages.PersistentMarking.HereditaryRestrictionProof
namespace LogicLineages.PersistentMarking.HereditaryAggregateCongruenceProof
open Spine NameBridge DecisionPorts FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics HereditaryLatticeTargets

theorem mapsEqual {α β γ : Type} (R : α → β → Prop) (f : α → γ) (g : β → γ)
    (hfg : ∀ a b, R a b → f a = g b) {xs : List α} {ys : List β} (h : Pointwise R xs ys) :
    xs.map f = ys.map g := by
  induction h with
  | nil => rfl
  | cons hab ht ih => simp only [List.map_cons,hfg _ _ hab,ih]

theorem bitsEqual {α β : Type} (R : α → β → Prop) (f : α → Bool) (g : β → Bool)
    (hfg : ∀ a b, R a b → f a = g b) {xs : List α} {ys : List β} (h : Pointwise R xs ys) :
    xs.all f = ys.all g ∧ xs.any f = ys.any g := by
  induction h with
  | nil => exact ⟨rfl,rfl⟩
  | cons hab ht ih => simp only [List.all_cons,List.any_cons,hfg _ _ hab,ih.1,ih.2]; exact ⟨rfl,rfl⟩

theorem congruence : AggregateCongruence := by
  intro E σ Γ meet xs ys h Δ hw he
  have ha := bitsEqual (ValueEq E σ Γ) (fun v => v.available Δ) (fun v => v.available Δ)
    (fun a b hab => (hab Δ hw he).1) h
  refine ⟨?_,?_,?_⟩
  · simp only [aggregate,ha.1,ha.2]
  · intro t ht
    have hweak := bitsEqual (ValueEq E σ Γ) (fun v => v.weak Δ t) (fun v => v.weak Δ t)
      (fun a b hab => ((hab Δ hw he).2.1 t ht).1) h
    have hstrict := bitsEqual (ValueEq E σ Γ) (fun v => v.strict Δ t) (fun v => v.strict Δ t)
      (fun a b hab => ((hab Δ hw he).2.1 t ht).2) h
    simp only [aggregate,hweak.1,hweak.2,hstrict.1,hstrict.2]
    exact ⟨rfl,rfl⟩
  · intro ds τ hp vs hv
    have hm := mapsEqual (ValueEq E σ Γ) (fun v => v.application Δ ds τ vs)
      (fun v => v.application Δ ds τ vs) (fun a b hab => (hab Δ hw he).2.2 ds τ hp vs hv) h
    simp only [aggregate,hm]

theorem restriction : AggregateRestriction := by
  intro E σ Γ Θ meet cs hΓ hΘ he hc
  have hp : Pointwise (ValueEq E σ Θ)
      (cs.map (HereditaryDomainSemantics.decode E σ Γ))
      ((cs.map ((descriptor E σ).restrict Γ Θ)).map (HereditaryDomainSemantics.decode E σ Θ)) := by
    induction cs with
    | nil => exact .nil
    | cons c cs ih =>
      apply Pointwise.cons
      · have h := (HereditaryRestrictionProof.restriction E σ Γ Θ hΓ hΘ he c (hc c List.mem_cons_self)).2
        intro Δ hw hd
        have h := h Δ hw hd
        exact ⟨h.1.symm,fun t ht => ⟨(h.2.1 t ht).1.symm,(h.2.1 t ht).2.symm⟩,
          fun ds τ hp vs hv => (h.2.2 ds τ hp vs hv).symm⟩
      · exact ih (fun x hx => hc x (List.mem_cons_of_mem _ hx))
  exact congruence E σ Θ meet _ _ hp
end LogicLineages.PersistentMarking.HereditaryAggregateCongruenceProof
