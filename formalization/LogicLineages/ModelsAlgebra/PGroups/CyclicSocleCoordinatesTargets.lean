module

public import LogicLineages.ModelsAlgebra.PGroups.CyclicSocleCoordinatesDefinitions

@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupInfinitary

def groupCyclicSocleCoordinateInjective : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (j : ℕ), Function.Injective (cyclicSocleCoordinate p j)

def groupCyclicSocleCoordinateRange : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (j : ℕ),
    (cyclicSocleCoordinate p j).range =
      (nsmulAddMonoidHom p : ZMod (p ^ (j+1)) →+ ZMod (p ^ (j+1))).ker

/-- Coherence, not merely some abstract isomorphism of the cyclic socle. -/
def groupCyclicSocleRootComposition : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : Type) [AddCommGroup G] (j : ℕ) (y : G)
    (hy : p ^ (j+1) • y = 0) (a : ZMod p),
    cyclicRootHom (p ^ (j+1)) G y hy (cyclicSocleCoordinate p j a) = a.val • (p ^ j • y)

end LogicLineages.ModelsAlgebra.PGroups.Targets
