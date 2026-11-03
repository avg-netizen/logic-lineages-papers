module
public import LogicLineages.OrdinalComparison.LayeredComparison.CommonHeadCompilerDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.CommonHeadCode
open CommonHeadLargeGuards
open LayeredComparison.CommonHeadCompiler
abbrev Code:=List Instruction

def constant (b:Bool):Code:=[(if b then 1 else 0,0,0)]
def conjunction (p q:Code):Code:=p++q++[(6,0,0)]
def disjunction (p q:Code):Code:=p++q++[(7,0,0)]
def negative (p:Code):Code:=p++[(5,0,0)]
def conjoin (ps:List Code):Code:=ps.foldr conjunction (constant true)
def disjoin (ps:List Code):Code:=ps.foldr disjunction (constant false)

def maskCode (m i:Nat) (mask:List Bool):Code:=
  conjoin ((List.range m).map (fun j=>
    if mask.getD j false then [(2,i,j)] else negative [(2,i,j)]))
def blockCode (cs:List Int) (i:Nat) (desired:Int):Code:=
  disjoin (((masks cs.length).filter (fun mask=>Int.sign (maskCoefficient cs mask)=desired)).map
    (maskCode cs.length i))
def canceledCode (cs:List Int):Code:=conjoin ((List.range cs.length).map (fun i=>blockCode cs i 0))
def maximalCode (cs:List Int) (i:Nat):Code:=
  conjoin ((List.range cs.length).map (fun j=>disjunction (negative [(3,i,j)]) (blockCode cs j 0)))
def signCode (K:Int) (cs:List Int) (desired:Int):Code:=
  disjunction (conjunction (constant (decide (Int.sign K=desired))) (canceledCode cs))
    (if desired=0 then constant false else disjoin ((List.range cs.length).map (fun i=>
      conjunction (blockCode cs i desired) (maximalCode cs i))))
def largeCode (K:Int) (cs:List Int) (desired:Int):Code:=
  conjunction (conjoin ((List.range cs.length).map (fun i=>[(4,originalThreshold K cs,i)])))
    (signCode K cs desired)

def renameInstruction (σ:Nat→Nat) (a:Instruction):Instruction:=
  if a.1=2 ∨ a.1=3 then (a.1,σ a.2.1,σ a.2.2)
  else if a.1=4 then (4,a.2.1,σ a.2.2) else a

def skipCode (i:Nat) (p:Code):Code:=p.map (renameInstruction (CommonHeadGuardReindex.skip i))
def guardedCode (i c:Nat) (p:Code):Code:=
  conjunction (conjunction [(4,c,i)] (negative [(4,c+1,i)])) (skipCode i p)

abbrev Input:=Nat×Nat×Int×List Int×Int
noncomputable def branchKeys (h:Nat) (K:Int) (cs:List Int):List (Nat×Nat):=
  (List.range cs.length).flatMap (fun i=>(smallNumerals h K cs).map (fun c=>(i,c)))
noncomputable def children (a:Input):List Input:=
  match a.1 with
  | 0=>[]
  | n+1=>(branchKeys a.2.1 a.2.2.1 a.2.2.2.1).map (fun key=>
      (n,a.2.1,childConstant a.2.1 a.2.2.1 a.2.2.2.1 key.1 key.2,
        a.2.2.2.1.eraseIdx key.1,a.2.2.2.2))
noncomputable def assemble (a:Input) (results:List Code):Code:=
  match a.1 with
  | 0=>constant (decide (Int.sign a.2.2.1=a.2.2.2.2))
  | _+1=>disjunction (largeCode a.2.2.1 a.2.2.2.1 a.2.2.2.2)
      (disjoin (List.zipWith (fun key p=>guardedCode key.1 key.2 p)
        (branchKeys a.2.1 a.2.2.1 a.2.2.2.1) results))
noncomputable def recursiveCode (a:Input):Code:=
  encode (compileFuel a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2)
end LogicLineages.OrdinalComparison.LayeredComparison.CommonHeadCode
