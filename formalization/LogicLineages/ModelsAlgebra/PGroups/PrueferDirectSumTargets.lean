module
public import LogicLineages.ModelsAlgebra.PGroups.PrueferDirectSumDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
def prueferDirectSumNature : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (I : Type), GroupDivisible (PrueferDirectSum p I) ∧
    ∀ x : PrueferDirectSum p I, ∃ k : ℕ, p^k • x = 0
/-- Exact coordinates from an actual model-socle isomorphism, instantiated internally
from the proved literal model when constructing the final decomposition. -/
def prueferDirectSumSocle : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (I : Type)
    (e : ZMod p ≃+ pSocle p (⊤ : AddSubgroup (PrueferModel p))),
    ∃ c : pSocle p (⊤ : AddSubgroup (PrueferDirectSum p I)) ≃+ (I →₀ ZMod p),
      ∀ x i, (e (c x i) : PrueferModel p) = (x:PrueferDirectSum p I) i
end LogicLineages.ModelsAlgebra.PGroups.Targets
