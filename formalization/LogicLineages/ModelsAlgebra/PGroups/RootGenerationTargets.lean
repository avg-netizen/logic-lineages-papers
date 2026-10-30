module

public import LogicLineages.ModelsAlgebra.PGroups.UlmBasisLiftTargets
public import Mathlib.Algebra.Group.Subgroup.Lattice

@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets

/-- Actual generation by cyclic lifts, not a decomposition/categoricity field.
Filtered socle spanning must supply only levels high enough for each root. -/
def groupUlmRootsGenerate : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : Type) [AddCommGroup G] (N : ℕ),
    (∀ g : G, p ^ N • g = 0) → ∀ (I : Fin N → Type)
    (b : ∀ l : Fin N, Module.Basis (I l) (ZMod p) (UlmLayer p (finiteFiltration p l.val : AddSubgroup G)))
    (x : ∀ l : Fin N, I l → pSocle p (finiteFiltration p l.val : AddSubgroup G))
    (y : ∀ l : Fin N, I l → G),
    (∀ l i, QuotientAddGroup.mk' (successorSocleSubgroup p (finiteFiltration p l.val)) (x l i) = b l i) →
    (∀ l i, p ^ l.val • y l i = (x l i : G)) →
      AddSubgroup.closure (Set.range (fun a : Σ l : Fin N, I l => y a.1 a.2)) = ⊤

/-- Generic bounded-group kernel detection. The eventual direct-sum
application must separately prove the displayed socle-kernel condition. -/
def groupBoundedSocleDetectsInjectivity : Prop :=
  ∀ (p N : ℕ) (A B : Type) [AddCommGroup A] [AddCommGroup B]
    (f : A →+ B), (∀ a : A, p ^ N • a = 0) →
    (∀ a : A, p • a = 0 → f a = 0 → a = 0) → Function.Injective f

end LogicLineages.ModelsAlgebra.PGroups.Targets
