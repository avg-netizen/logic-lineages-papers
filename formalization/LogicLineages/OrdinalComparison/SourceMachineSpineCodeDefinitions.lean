module
public import LogicLineages.OrdinalComparison.SourceBinarySpineCodeDefinitions
public import LogicLineages.OrdinalComparison.SourceMachineConjunctionPlanDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceMachineSpineCode
open SourcePlanSpineCode SourcePrimitiveForestCode
/-- Literal one-based ports in the original thirteen-wire context. -/
def remainder : List Instruction :=
  [(2,11,8,4),(1,4,3,0),(2,13,13,5),(2,5,7,6),(1,12,6,0),
    (0,successorCode 11,portCode 12,0)]
def tail (e : Nat) : List Instruction :=
  (2,10,10,1)::(2,1,9,2)::SourceScalingSpineCode.build e 2 3 remainder
/-- Continuation is already in the constant's extended context. -/
def constant (k : Nat) (is : List Instruction) : List Instruction :=
  (4,0,0,0)::SourceBinarySpineCode.build k 1 is
def code (b e : Nat) : List Instruction :=
  constant (2*b+5) (constant 4 (constant 1 (List.replicate 6 (4,0,0,0) ++ tail e)))
def compiled (b e : Nat) : State := run (code b e)
/-- Ordered as (L,R); strict comparison is R<L, not L<R. -/
def aggregate (b e : Nat) : Nat × Nat := SourcePlanSpineCode.aggregateCode (code b e)
end LogicLineages.OrdinalComparison.Source.SourceMachineSpineCode
