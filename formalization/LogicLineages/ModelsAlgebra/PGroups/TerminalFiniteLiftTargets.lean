module
public import LogicLineages.ModelsAlgebra.PGroups.TerminalFiniteLiftDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets

def terminalFiniteLift : Prop :=
  ∀ (G : Type) [AddCommGroup G] (p : ℕ) [Fact p.Prime],
    (∀ x : G, ∃ n : ℕ, p^n • x = 0) →
    ∀ (γ : Ordinal.{0}) (A K T : AddSubgroup G),
    (transfiniteFiltration p (Ordinal.omega0 * γ) : AddSubgroup G) = K ⊔ T →
    Disjoint K T → A ⊓ transfiniteFiltration p (Ordinal.omega0 * γ) ≤ K →
    ∀ (D : AddSubgroup (G ⧸ T)) [Finite D]
      (hAD : A.map (QuotientAddGroup.mk' T) ≤ D),
    ∃ F : D →+ G, Function.Injective F ∧
      (∀ a : A, F ⟨(QuotientAddGroup.mk' T) a, hAD ⟨a,a.property,rfl⟩⟩ = (a:G)) ∧
      ∀ (y : D) (β : Ordinal.{0}), β ≤ Ordinal.omega0 * γ →
        (F y ∈ (transfiniteFiltration p β : AddSubgroup G) ↔
          (y:G ⧸ T) ∈ (transfiniteFiltration p β : AddSubgroup (G ⧸ T)))
end LogicLineages.ModelsAlgebra.PGroups.Targets
