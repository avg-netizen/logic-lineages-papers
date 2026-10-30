module

public import LogicLineages.ModelsAlgebra.PGroups.PowerCyclicDefinitions
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Finsupp.Encodable
public import Mathlib.Algebra.Group.Pi.Lemmas
public import Mathlib.Algebra.Group.Prod

@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
open scoped BigOperators

abbrev BlockShiftGroup (p k t : ℕ) (ℓ : Fin t → ℕ) :=
  (∀ j : Fin t, ZMod (p ^ ℓ j)) × (ℕ →₀ ZMod (p ^ k))

/-- Actual finite sum of disjoint coordinate insertions. -/
noncomputable def finiteBlockInsert (p k t : ℕ) (ℓ : Fin t → ℕ) (h : ∀ j, ℓ j ≤ k) :
    (∀ j : Fin t, ZMod (p ^ ℓ j)) →+ (ℕ →₀ ZMod (p ^ k)) :=
  ∑ j : Fin t, ((Finsupp.singleAddHom j.val).comp (powerCyclicInclusion p (ℓ j) k (h j))).comp
    (Pi.evalAddMonoidHom (fun j : Fin t => ZMod (p ^ ℓ j)) j)

noncomputable def blockShiftHom (p k t : ℕ) (ℓ : Fin t → ℕ) (h : ∀ j, ℓ j ≤ k) :
    BlockShiftGroup p k t ℓ →+ BlockShiftGroup p k t ℓ :=
  let tail : (ℕ →₀ ZMod (p ^ k)) →+ (ℕ →₀ ZMod (p ^ k)) :=
    Finsupp.mapDomain.addMonoidHom (fun i : ℕ => t + i)
  (0 : BlockShiftGroup p k t ℓ →+ (∀ j : Fin t, ZMod (p ^ ℓ j))).prod
    ((finiteBlockInsert p k t ℓ h).comp (AddMonoidHom.fst _ _) + tail.comp (AddMonoidHom.snd _ _))

/-- An actual socle element in the designated short factor. -/
noncomputable def blockShortWitness (p k t : ℕ) (ℓ : Fin t → ℕ) (j : Fin t) :
    BlockShiftGroup p k t ℓ :=
  (Pi.single j (((p ^ (ℓ j - 1) : ℕ) : ZMod (p ^ ℓ j))), 0)

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
