module
public import LogicLineages.ModelsAlgebra.PGroups.LowerUlmDescriptorDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupInfinitary

def lowerUlmDescriptor : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : Type) [AddCommGroup G] [Countable G]
    (γ : Ordinal.{0}) [Countable γ.ToType],
    ∃ φ : Formula 0, Complexity .pi (2*γ+1) φ ∧
      ∀ (H : Type) [AddCommGroup H] [Countable H],
        φ.Realize (Fin.elim0 : Fin 0 → H) ↔
          ∀ α < Ordinal.omega0*γ,
            Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p α : AddSubgroup G)) =
            Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p α : AddSubgroup H))
end LogicLineages.ModelsAlgebra.PGroups.Targets
