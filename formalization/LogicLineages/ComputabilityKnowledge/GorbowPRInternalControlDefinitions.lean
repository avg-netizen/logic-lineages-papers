module

public import LogicLineages.ComputabilityKnowledge.GorbowPRInternalArithmeticDefinitions

@[expose] public section
/-! Literal finite PR ASTs for zero testing and conditional control. Uniform
internal correctness is a separate object-language proof, not inferred from
standard evaluation. The conditional reads [control, zero-branch, other]. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowPRInternalControl
open GorbowPRProgram

def one : Program 0 := .composition .succ (fun _ : Fin 1 => .zero)
def zeroStep : Program 2 := .composition .zero Fin.elim0
def zeroTest : Program 1 := .recursion one zeroStep

def conditional : Program 3 :=
  .recursion (.projection (0 : Fin 2)) (.projection (3 : Fin 4))

end LogicLineages.ComputabilityKnowledge.GorbowPRInternalControl
