module
public import LogicLineages.OrdinalComparison.BinaryPartitionSeriesDefinitions

@[expose] public section

namespace LogicLineages.OrdinalComparison

/-- Literal zeroth coordinate basis vector, with the empty vector at D=0. -/
def actualBinaryInitialVector (D : Nat) : Fin D → ZMod 2 :=
  fun i => if i.val = 0 then 1 else 0

end LogicLineages.OrdinalComparison
