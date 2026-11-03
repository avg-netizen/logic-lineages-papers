module
public import LogicLineages.OrdinalComparison.LayeredComparison.CommonLayerComparisonDefinitions
public import LogicLineages.OrdinalComparison.LayeredComparison.FiniteGraphDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.CommonLayerProgram
open CommonLayerComparison CommonLayerSyntax CommonHeadCompiler
abbrev Input:=List Nat×Nat×Nat×Int
abbrev Code:=List Instruction

def baseCode (E F:Nat) (desired:Int):Code:=
  if desired=0 then [(2,E,F)]
  else if desired= -1 then [(3,E,F)]
  else if desired=1 then [(3,F,E)]
  else [(0,0,0)]

noncomputable def rowCode (h E F:Nat) (desired:Int):Code:=
  CommonHeadCompiler.compileCode h (rowConstant E F) (rowCoefficients E F) desired

/-- Every row instruction has one strictly lower-layer child. Children of
Boolean instructions are harmless constant comparisons and are ignored; this
keeps the exact original instruction/occurrence order without an index oracle. -/
def child (Γ:List Nat) (N:Nat) (args:List Nat) (q:Instruction):Input:=
  if q.1=2 then (Γ,args.getD q.2.1 (constantCode Γ.length 0),
    args.getD q.2.2 (constantCode Γ.length 0),0)
  else if q.1=3 then (Γ,args.getD q.2.1 (constantCode Γ.length 0),
    args.getD q.2.2 (constantCode Γ.length 0),-1)
  else if q.1=4 then (Γ,args.getD q.2.2 (constantCode Γ.length 0),
    constantCode Γ.length (q.2.1-N),-1)
  else (Γ,constantCode Γ.length 0,constantCode Γ.length 0,0)

def instructionCode (N:Nat) (q:Instruction) (result:Code):Code:=
  if q.1=2 then result
  else if q.1=3 then result
  else if q.1=4 then if q.2.1≤N then [(1,0,0)] else result++[(5,0,0)]
  else [q]

noncomputable def children (a:Input):List Input:=
  match a.1 with
  | []=>[]
  | h::Γ=>(rowCode h a.2.1 a.2.2.1 a.2.2.2).map
      (child Γ (rawNormCode h) (rowArguments a.2.1 a.2.2.1))

noncomputable def assemble (a:Input) (results:List Code):Code:=
  match a.1 with
  | []=>baseCode a.2.1 a.2.2.1 a.2.2.2
  | h::_=>((rowCode h a.2.1 a.2.2.1 a.2.2.2).zipWith
      (instructionCode (rawNormCode h)) results).flatten

noncomputable def recursiveCode (a:Input):Code:=CommonLayerComparison.compileCode a.1 a.2.1 a.2.2.1 a.2.2.2

def measure (a:Input):Nat:=a.1.length
end LogicLineages.OrdinalComparison.LayeredComparison.CommonLayerProgram
