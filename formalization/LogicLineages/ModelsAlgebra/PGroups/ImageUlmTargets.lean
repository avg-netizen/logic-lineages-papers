module
public import LogicLineages.ModelsAlgebra.PGroups.ImageFiltrationTargets
public import Mathlib.LinearAlgebra.Dimension.Basic
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupInfinitary

def groupImageUlmIsomorphism : Prop :=
  ∀ (G : Type) [AddCommGroup G] (p k j : ℕ),
    Nonempty (UlmLayer p (finiteFiltration p j : AddSubgroup (multipleImage G (p ^ k))) ≃ₗ[ZMod p]
      UlmLayer p (finiteFiltration p (k+j) : AddSubgroup G))

def groupImageUlmRank : Prop :=
  ∀ (G : Type) [AddCommGroup G] (p k j : ℕ),
    Module.rank (ZMod p) (UlmLayer p (finiteFiltration p j : AddSubgroup (multipleImage G (p ^ k)))) =
      Module.rank (ZMod p) (UlmLayer p (finiteFiltration p (k+j) : AddSubgroup G))

end LogicLineages.ModelsAlgebra.PGroups.Targets
