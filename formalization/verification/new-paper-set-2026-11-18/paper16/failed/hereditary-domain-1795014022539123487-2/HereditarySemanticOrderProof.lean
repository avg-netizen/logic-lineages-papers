import LogicLineages.PersistentMarking.HereditaryOrderTargets
import LogicLineages.PersistentMarking.FinitePrefixProof
namespace LogicLineages.PersistentMarking.HereditarySemanticOrderProof
open Spine NameBridge DecisionPorts FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics HereditaryOrderTargets

theorem boolAntisymm (a b : Bool) (h : a=true → b=true) (k : b=true → a=true) : a=b := by
  cases a <;> cases b <;> simp_all

theorem laws : SemanticOrderLaws := by
  intro E σ Γ hw lower
  constructor
  · intro a ha Δ hd he
    refine ⟨id,fun t ht => ⟨id,id⟩,?_⟩
    intro ds τ hp vs hv
    exact (lower τ (FinitePrefixProof.proper σ ds τ hp).1 Δ hd).1 _ (ha.1 Δ hd he ds τ hp vs hv)
  constructor
  · intro a b c ha hb hc hab hbc Δ hd he
    have h := hab Δ hd he
    have k := hbc Δ hd he
    refine ⟨fun x => k.1 (h.1 x),fun t ht => ⟨fun x => (k.2.1 t ht).1 ((h.2.1 t ht).1 x),
      fun x => (k.2.1 t ht).2 ((h.2.1 t ht).2 x)⟩,?_⟩
    intro ds τ hp vs hv
    exact (lower τ (FinitePrefixProof.proper σ ds τ hp).1 Δ hd).2.1 _ _ _
      (ha.1 Δ hd he ds τ hp vs hv) (hb.1 Δ hd he ds τ hp vs hv) (hc.1 Δ hd he ds τ hp vs hv)
      (h.2.2 ds τ hp vs hv) (k.2.2 ds τ hp vs hv)
  · intro a b ha hb hab hba Δ hd he
    have h := hab Δ hd he
    have k := hba Δ hd he
    refine ⟨boolAntisymm _ _ h.1 k.1,fun t ht => ⟨boolAntisymm _ _ (h.2.1 t ht).1 (k.2.1 t ht).1,
      boolAntisymm _ _ (h.2.1 t ht).2 (k.2.1 t ht).2⟩,?_⟩
    intro ds τ hp vs hv
    exact (lower τ (FinitePrefixProof.proper σ ds τ hp).1 Δ hd).2.2 _ _
      (ha.1 Δ hd he ds τ hp vs hv) (hb.1 Δ hd he ds τ hp vs hv)
      (h.2.2 ds τ hp vs hv) (k.2.2 ds τ hp vs hv)
end LogicLineages.PersistentMarking.HereditarySemanticOrderProof
