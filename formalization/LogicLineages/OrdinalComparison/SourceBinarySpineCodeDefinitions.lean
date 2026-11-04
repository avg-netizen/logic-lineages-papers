module
public import LogicLineages.OrdinalComparison.SourceBinaryHalvingTraceDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceBinarySpineCode
open SourcePlanSpineCode SourcePrimitiveForestCode SourceAdditionCompletion
abbrev BinaryState := Nat × Nat × List Instruction
/-- State is accumulated existential prefix count, output port, continuation. -/
def advance (bit : Nat) (s : BinaryState) : BinaryState :=
  if bit=0 then
    (s.1+1,1,(2,1,1,shiftPort 1 s.2.1)::SourcePlanInsertionCode.insert 0 1 s.2.2)
  else
    (s.1+3,3,(2,3,3,2)::(3,1,0,0)::(2,2,1,shiftPort 3 s.2.1)::SourcePlanInsertionCode.insert 0 3 s.2.2)
def terminal (base out : Nat) : Instruction :=
  if base=0 then (1,out,0,0) else (3,out,0,0)
/-- bits are outer-to-inner. A nonzero raw bit uses doubleOne. -/
def buildBits (bits : List Nat) (base out : Nat) (is : List Instruction) : List Instruction :=
  let s := bits.foldl (fun s b => advance b s) (0,out,is)
  List.replicate s.1 (4,0,0,0) ++ terminal base s.2.1::s.2.2
/-- The accepted trace is inner-to-outer, hence this explicit reversal. -/
def build (k out : Nat) (is : List Instruction) : List Instruction :=
  let t := SourceBinaryHalvingTrace.trace k
  buildBits t.2.reverse t.1 out is

def dagOfBits (bits : List Nat) (base : Nat) : BinaryDAG :=
  bits.foldr (fun b d => SourceBinaryHalvingTrace.wrap d b) (if base=0 then .zero else .one)
end LogicLineages.OrdinalComparison.Source.SourceBinarySpineCode
