module
public import LogicLineages.OrdinalComparison.SourcePlanSpineCodeDefinitions
public import LogicLineages.OrdinalComparison.SourceBinaryPlanDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourcePlanInsertionCode
open SourcePlanSpineCode

def portInsert (depth count p : Nat) : Nat :=
  if p=0 then 0 else if p-1<depth then p else p+count

def instruction (depth count : Nat) (i : Instruction) : Instruction :=
  if i.1=0 then (0,ContextInsertionCode.sourceCode depth count i.2.1,
    ContextInsertionCode.sourceCode depth count i.2.2.1,i.2.2.2)
  else if i.1=1 then (1,portInsert depth count i.2.1,portInsert depth count i.2.2.1,i.2.2.2)
  else if i.1=2 then (2,portInsert depth count i.2.1,portInsert depth count i.2.2.1,portInsert depth count i.2.2.2)
  else if i.1=3 then (3,portInsert depth count i.2.1,i.2.2.1,i.2.2.2)
  else i

def nextDepth (depth : Nat) (i : Instruction) : Nat := if i.1=4 then depth+1 else depth
/-- Left scan retains reversed output and protects one more coordinate at each
actual existential instruction; gates allocate no syntactic binder. -/
def scanStep (count : Nat) (s : Nat × List Instruction) (i : Instruction) : Nat × List Instruction :=
  (nextDepth s.1 i,instruction s.1 count i::s.2)
def insert (depth count : Nat) (is : List Instruction) : List Instruction :=
  (is.foldl (scanStep count) (depth,[])).2.reverse
end LogicLineages.OrdinalComparison.Source.SourcePlanInsertionCode
