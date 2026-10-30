module
public import LogicLineages.ModelsAlgebra.PGroups.PrimeExtensionDefinitions
public import Mathlib.Data.Nat.Prime.Defs
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
universe u

def groupPrimeExtensionKernel : Prop :=
  ∀ (G H : Type u) [AddCommGroup G] [AddCommGroup H] (p : ℕ) [Fact p.Prime]
    (B : AddSubgroup G) (x : G), x ∉ B → ∀ hpx : p • x ∈ B,
    ∀ (f : B →+ H), Function.Injective f → ∀ w : H,
    w ∉ f.range → p • w = f ⟨p • x,hpx⟩ →
    (adjunctionHom G B x).ker = (mappedAdjunctionHom G H B f w).ker

end LogicLineages.ModelsAlgebra.PGroups.Targets
