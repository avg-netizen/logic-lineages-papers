module
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealCoverAssemblyDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.RankedIdealCover
open RankedParse RankedIdealRank RankedIdealComponents RankedIdealCompletion RankedIdealRegularCode RankedIdealSpineCode RankedIdealCoverAssembly
/-- Finite literal test for a productive binary transition wholly in one SCC. -/
def nonlinear (C : Code) (q : C.machine.State) : Bool :=
  ops.any fun o => C.states.any fun x => C.states.any fun y =>
    decide (x ∈ productive C.machine ∧ y ∈ productive C.machine ∧
      SameComponent C.machine q x ∧ SameComponent C.machine q y ∧
      SameComponent C.machine q (C.machine.node o x y))
/-- Structurally terminating finite-state ideal decomposition. The fuel bound
is proved sufficient by strict epsilon-predecessor cardinality descent. -/
def pieces (C : Code) : Nat → C.machine.State → List Code
  | 0, _ => []
  | n+1, q =>
      if q ∈ productive C.machine then
        if nonlinear C q = true then [component C q]
        else linearPieces C q (pieces C n)
      else []
/-- Explicit accepting-state enumeration. Every output is an actual finite
regular machine with its executable state list, never a semantic ideal oracle. -/
def cover (C : Code) : List Code :=
  C.states.flatMap fun q => if C.machine.accept q = true then
    pieces C (Fintype.card C.machine.State) q else []
end LogicLineages.ModelsAlgebra.Forests.RankedIdealCover
