module
public import LogicLineages.ModelsAlgebra.PGroups.SoclePullbackDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
/-- Exact transfinite filtration of an actual pullback from a divisible group,
assuming only the literal below-cut socle-surjectivity of its other map. -/
def actualSoclePullbackFiltration : Prop :=
  ∀ (p:ℕ) (B C E:Type) [AddCommGroup B] [AddCommGroup C] [AddCommGroup E]
    (f:B→+C) (q:E→+C) (δ:Ordinal.{0}),
    p≠0 → Function.Surjective q → GroupDivisible E →
    (∀β:Ordinal.{0},β<δ→∀c:pSocle p (⊤:AddSubgroup C),
      ∃b:pSocle p (transfiniteFiltration p β:AddSubgroup B),f (b:B)=(c:C)) →
    Function.Surjective (pullbackProjection f q) ∧
    ∀α:Ordinal.{0},α≤δ→∀x:HomPullback f q,
      x∈(transfiniteFiltration p α:AddSubgroup (HomPullback f q)) ↔
      x.val.1∈(transfiniteFiltration p α:AddSubgroup B)
end LogicLineages.ModelsAlgebra.PGroups.Targets
