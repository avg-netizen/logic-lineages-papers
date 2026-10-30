module

public import LogicLineages.ModelsAlgebra.PGroups.BlockShiftDefinitions
public import LogicLineages.ModelsAlgebra.PGroups.UpperCyclicDefinitions
public import Mathlib.Data.Finset.Lattice.Fold

@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary

abbrev FullShiftGroup (p k t : ℕ) (ℓ : Fin t → ℕ) (s : ℕ) (r : Fin s → ℕ) :=
  BlockShiftGroup p k t ℓ × UpperCyclicGroup p s r

noncomputable def fullShiftHom (p k t : ℕ) (ℓ : Fin t → ℕ) (h : ∀ j, ℓ j ≤ k)
    (s : ℕ) (r : Fin s → ℕ) : FullShiftGroup p k t ℓ s r →+ FullShiftGroup p k t ℓ s r :=
  (blockShiftHom p k t ℓ h).prodMap (AddMonoidHom.id (UpperCyclicGroup p s r))

def fullExponentBound (k s : ℕ) (r : Fin s → ℕ) : ℕ := max k (Finset.univ.sup r)

noncomputable def fullShortWitness (p k t : ℕ) (ℓ : Fin t → ℕ) (s : ℕ) (r : Fin s → ℕ)
    (j : Fin t) : FullShiftGroup p k t ℓ s r :=
  (blockShortWitness p k t ℓ j, 0)

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
