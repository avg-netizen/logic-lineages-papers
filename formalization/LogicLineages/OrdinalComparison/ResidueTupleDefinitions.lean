module
public import LogicLineages.OrdinalComparison.LinkedResidueLaurentDefinitions
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.Dynamics.PeriodicPts.Defs

@[expose] public section
namespace LogicLineages.OrdinalComparison

abbrev ActualResidueField := AlgebraicClosure (ZMod 2)
abbrev ActualPrimitiveRootIndex (u : Nat) :=
  {z : ActualResidueField // IsPrimitiveRoot z (actualLinkedModulus u)}

noncomputable def actualResidueTuple (u : Nat) : ActualPrimitiveRootIndex u → ActualResidueField :=
  fun z => (actualLinkedResidueExpansion u z.val).coeff (-1)

noncomputable def actualResidueTupleFrobenius (u : Nat)
    (v : ActualPrimitiveRootIndex u → ActualResidueField) :
    ActualPrimitiveRootIndex u → ActualResidueField := fun z => v z ^ 2

end LogicLineages.OrdinalComparison
