module

public import LogicLineages.ComputabilityKnowledge.RayMapDifference

@[expose] public section

/-! The actual finite support after discarding zero affine differences,
as required before selecting the source's greatest surviving key.
-/
namespace LogicLineages.ComputabilityKnowledge.RaySurvivingDifference

open ExponentialNormalForm RayMapDifference

noncomputable def survivingKeys {d h : Nat} (f g : Form d (h + 1)) : Finset (Form d h) := by
  classical
  exact (keySet f g).filter (fun key => f key ≠ g key)

end LogicLineages.ComputabilityKnowledge.RaySurvivingDifference
