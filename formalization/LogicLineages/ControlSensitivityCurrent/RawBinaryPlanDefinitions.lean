module
public import LogicLineages.ControlSensitivityCurrent.RawPlanRenamingDefinitions
public import LogicLineages.OrdinalComparison.SourceBinaryHalvingTraceDefinitions
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.RawSourceDAG.BinaryPlanCompiler

open LogicLineages.OrdinalComparison.Source.SourceBinaryHalvingTrace (TraceState trace)
open PlanCompiler (Instruction)

abbrev BinaryState := List Nat × Nat × List Instruction × Nat

def binder : Instruction := .inr (.inr PUnit.unit)

def gate (g : PrimitiveGate.GateCode) : Instruction := .inr (.inl g)

def shiftPort (n p : Nat) : Nat := if p = 0 then 0 else p + n

def prefixTable (n : Nat) (context : List Nat) : List Nat :=
  (List.range context.length).map (fun i => i + n)

def binaryStep (s : BinaryState) (bit : Nat) : BinaryState :=
  let (context,out,tail,pending) := s
  if bit = 0 then
    let target := 0 :: context
    (target, 1, gate (1,1,1,shiftPort 1 out,0) ::
      PlanRenaming.renamePlanRaw target (prefixTable 1 context) tail, pending + 1)
  else
    let target := 0 :: 0 :: 0 :: context
    (target, 3, gate (1,3,3,2,0) :: gate (3,1,0,0,0) :: gate (1,2,1,shiftPort 3 out,0) ::
      PlanRenaming.renamePlanRaw target (prefixTable 3 context) tail, pending + 3)

def finish (base : Nat) (state : BinaryState) : List Instruction :=
  let (_,out,tail,pending) := state
  List.replicate pending binder ++
    (if base = 0 then gate (0,out,0,0,0) else gate (3,out,0,0,0)) :: tail

def lowerTrace (s : TraceState) (init : BinaryState) : List Instruction :=
  finish s.1 (s.2.reverse.foldl binaryStep init)

def constantRaw (context : List Nat) (k : Nat) (tail : List Instruction) : List Instruction :=
  lowerTrace (trace k) (0 :: context, 1, tail, 1)

end LogicLineages.ControlSensitivityCurrent.RawSourceDAG.BinaryPlanCompiler
