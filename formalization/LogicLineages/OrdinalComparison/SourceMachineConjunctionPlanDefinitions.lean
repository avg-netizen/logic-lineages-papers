module
public import LogicLineages.OrdinalComparison.ParametricScalingPlanDefinitions
public import LogicLineages.OrdinalComparison.SourceMachineHaltingConjunctionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceMachineConjunctionPlan
open PrimitiveLowering ExistentialPlan BinaryPlan ParametricScalingPlan
abbrev Base := List.replicate 4 Ty.ground
abbrev Wired := List.replicate 13 Ty.ground
def original (i : Fin 4) : Variable Base .ground := fresh (Γ:=[]) i
def wire (i : Fin 13) : Variable Wired .ground := fresh (Γ:=[]) i
def port (i : Fin 13) : Port Wired := .var (wire i)

/-- Slots 0..5: doubled t, sum, scaled value, z+4, doubled w, odd value.
Slots 6..8: one, four, C. Slots 9..12: original t,z,y,w. -/
def tail (e : Nat) : Plan Wired :=
  .gate (.add (port 9) (port 9) (port 0))
    (.gate (.add (port 0) (port 8) (port 1))
      (scalePlan e (port 1) (port 2)
        (.gate (.add (port 10) (port 7) (port 3))
          (.gate (.eq (port 3) (port 2))
            (.gate (.add (port 12) (port 12) (port 4))
              (.gate (.add (port 4) (port 6) (port 5))
                (.gate (.eq (port 11) (port 5))
                  (.equation (Expr.successor (port 10)).graph (Expr.port (port 11)).graph .done))))))))

/-- Three binary literal bindings, then six shared intermediate wires. -/
def plan (b e : Nat) : Plan Base :=
  constantPlan (SourceMachineHaltingConjunction.oddConstant b)
    (constantPlan 4 (constantPlan 1
      (.existsGround (.existsGround (.existsGround
        (.existsGround (.existsGround (.existsGround (tail e)))))))))
def bits (b : Nat) : Nat := Nat.log2 (SourceMachineHaltingConjunction.oddConstant b)+1
end LogicLineages.OrdinalComparison.Source.SourceMachineConjunctionPlan
