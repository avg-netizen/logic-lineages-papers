module

public import LogicLineages.ModelsAlgebra.PGroups.CyclicRootDefinitions
public import LogicLineages.ModelsAlgebra.PGroups.PowerCyclic

@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary

/-- Coherent p-socle coordinate: 1 maps to the literal p^j element. -/
noncomputable def cyclicSocleCoordinate (p : ℕ) [Fact p.Prime] (j : ℕ) :
    ZMod p →+ ZMod (p ^ (j+1)) :=
  cyclicRootHom p (ZMod (p ^ (j+1))) ((p ^ j : ℕ) : ZMod (p ^ (j+1)))
    (by simpa only [Nat.add_sub_cancel] using
      (power_cyclic_socle_witness p (j+1) (Nat.succ_pos j)).1)

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
