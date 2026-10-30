module

public import Mathlib.Topology.Instances.AddCircle.Real

@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets

/-- Literal finite cyclic image in the actual real additive circle. For
natural n, NeZero is exactly the positive-modulus restriction. -/
def groupCircleTorsionRange : Prop :=
  ∀ (n : ℕ) [NeZero n],
    (ZMod.toAddCircle : ZMod n →+ UnitAddCircle).range =
      (nsmulAddMonoidHom n : UnitAddCircle →+ UnitAddCircle).ker

def groupCircleTorsionIsomorphism : Prop :=
  ∀ (n : ℕ) [NeZero n], Nonempty (ZMod n ≃+
    (nsmulAddMonoidHom n : UnitAddCircle →+ UnitAddCircle).ker)

end LogicLineages.ModelsAlgebra.PGroups.Targets
