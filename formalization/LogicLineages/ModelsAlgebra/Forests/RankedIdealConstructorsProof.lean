module
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealConstructorsTargets
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealContextStatementChecks
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.RankedIdealConstructors.Proof
open RankedParse RankedIdealContext RankedGraphImage RankedIdealContext.Proof

theorem productIdeal : Targets.ProductIdeal := by
  intro o I J hI hJ
  constructor
  · obtain ⟨l, hl⟩ := hI.nonempty
    obtain ⟨r, hr⟩ := hJ.nonempty
    exact ⟨.node o l r, .node o l r, ⟨l, r, hl, hr, rfl⟩, embeddingReflexive _⟩
  · rintro s t hst ⟨u, hu, htu⟩
    exact ⟨u, hu, embeddingTransitive hst htu⟩
  · rintro s t ⟨_, ⟨l, r, hl, hr, rfl⟩, hs⟩ ⟨_, ⟨l', r', hl', hr', rfl⟩, ht⟩
    obtain ⟨a, ha, hla, hl'a⟩ := hI.directed l l' hl hl'
    obtain ⟨b, hb, hrb, hr'b⟩ := hJ.directed r r' hr hr'
    exact ⟨.node o a b, ⟨.node o a b, ⟨a, b, ha, hb, rfl⟩, embeddingReflexive _⟩,
      embeddingTransitive hs (.couple o hla hrb),
      embeddingTransitive ht (.couple o hl'a hr'b)⟩

private theorem star_directed (K : Context → Prop) (B : Term → Prop) (hB : IsIdeal B)
    s t (hs : Star K B s) (ht : Star K B t) :
    ∃ u, Star K B u ∧ Homeomorphic s u ∧ Homeomorphic t u := by
  induction hs generalizing t with
  | @base b hb =>
      induction ht with
      | @base b' hb' =>
          obtain ⟨u, hu, hbu, hb'u⟩ := hB.directed b b' hb hb'
          exact ⟨u, .base hu, hbu, hb'u⟩
      | @step c z hc hz ih =>
          obtain ⟨u, hu, hbu, hzu⟩ := ih
          exact ⟨plug c u, .step hc hu, embeddingTransitive hbu (holeEmbeds c u),
            plugMonotone c hzu⟩
  | @step c z hc hz ih =>
      obtain ⟨u, hu, hzu, htu⟩ := ih t ht
      exact ⟨plug c u, .step hc hu, plugMonotone c hzu,
        embeddingTransitive htu (holeEmbeds c u)⟩

theorem linearPieceIdeal : Targets.LinearPieceIdeal := by
  intro K B hB
  constructor
  · obtain ⟨b, hb⟩ := hB.nonempty
    exact ⟨b, b, .base hb, embeddingReflexive b⟩
  · rintro s t hst ⟨u, hu, htu⟩
    exact ⟨u, hu, embeddingTransitive hst htu⟩
  · rintro s t ⟨a, ha, hsa⟩ ⟨b, hb, htb⟩
    obtain ⟨u, hu, hau, hbu⟩ := star_directed K B hB a b ha hb
    exact ⟨u, ⟨u, hu, embeddingReflexive u⟩,
      embeddingTransitive hsa hau, embeddingTransitive htb hbu⟩

theorem contextSupport : Targets.ContextSupport := by
  intro K B c b s hc hb hs
  exact ⟨plug c b, .step hc (.base hb), hs⟩
end LogicLineages.ModelsAlgebra.Forests.RankedIdealConstructors.Proof
