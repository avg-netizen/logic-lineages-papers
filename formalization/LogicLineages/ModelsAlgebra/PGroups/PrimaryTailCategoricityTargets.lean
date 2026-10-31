module
public import LogicLineages.ModelsAlgebra.PGroups.PrimaryTailCategoricityDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
def divisiblePartInSubgroup : Prop :=
  ∀ (G:Type) [AddCommGroup G] (S:AddSubgroup G), divisiblePart G ≤ S →
    ∃ e:divisiblePart G ≃+ divisiblePart S, ∀x, (((e x:divisiblePart S):S):G)=(x:G)
def primaryTailCategoricity : Prop :=
  ∀ (G H:Type) [AddCommGroup G] [AddCommGroup H] [Countable G] [Countable H]
    (p:ℕ) [Fact p.Prime],
    (∀x:G,∃k:ℕ,p^k • x=0) → (∀x:H,∃k:ℕ,p^k • x=0) →
    ∀δ:Ordinal.{0},
    (transfiniteFiltration p δ:AddSubgroup G) ≃+ (transfiniteFiltration p δ:AddSubgroup H) →
    (∀α<δ, Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p α:AddSubgroup G)) =
      Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p α:AddSubgroup H))) →
    Nonempty (G≃+H)
end LogicLineages.ModelsAlgebra.PGroups.Targets
