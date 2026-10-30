module
public import LogicLineages.ModelsAlgebra.PGroups.UlmFiniteIndependenceTargets
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupInfinitary

/-- The genuine inclusion identifies image-internal filtration with ambient shifted filtration. -/
def groupImageFiniteFiltration : Prop :=
  ∀ (G : Type) [AddCommGroup G] (p k j : ℕ),
    (finiteFiltration p j : AddSubgroup (multipleImage G (p ^ k))).map
      (multipleImage G (p ^ k)).subtype =
        (finiteFiltration p (k+j) : AddSubgroup G)

/-- Same actual inclusion, with literal p-annihilation retained. -/
def groupImageFiniteSocle : Prop :=
  ∀ (G : Type) [AddCommGroup G] (p k j : ℕ),
    (pSocle p (finiteFiltration p j : AddSubgroup (multipleImage G (p ^ k)))).map
      (multipleImage G (p ^ k)).subtype =
        pSocle p (finiteFiltration p (k+j) : AddSubgroup G)

end LogicLineages.ModelsAlgebra.PGroups.Targets
