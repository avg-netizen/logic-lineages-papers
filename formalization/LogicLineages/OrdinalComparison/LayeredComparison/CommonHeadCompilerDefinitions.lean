module
public import LogicLineages.OrdinalComparison.CommonHeadGuardReindexDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.CommonHeadCompiler
open CommonHeadLargeRow CommonHeadLargeGuards

/-- Both the input occurrence and its entire argument remain labeled until
an equality guard fixes that argument to this closed numeral. -/
noncomputable def childConstant (h:Nat) (K:Int) (cs:List Int) (i c:Nat) : Int :=
  K+cs.getD i 0*(CommonHeadSmallFold.closedValueCode h c:Int)

def smallNumerals (h:Nat) (K:Int) (cs:List Int) : List Nat :=
  CommonHeadSmallFold.smallValuesCode h K (cs.map (fun a=>(a,0)))

/-- Literal occurrence-count recursion. The zero-fuel clause is used by the
exact theorem only for an empty row. Each child removes ONE occurrence and
recomputes its own ORIGINAL threshold with its new constant. -/
noncomputable def compileFuel : Nat→Nat→Int→List Int→Int→Formula
  | 0,_,K,_,desired => if Int.sign K=desired then .truth else .falsity
  | fuel+1,h,K,cs,desired =>
      .disj (largeFormula K cs desired)
        (disjunction ((List.range cs.length).flatMap (fun i=>
          (smallNumerals h K cs).map (fun c=>CommonHeadGuardReindex.guarded i c
            (compileFuel fuel h (childConstant h K cs i c) (cs.eraseIdx i) desired)))))

noncomputable def compile (h:Nat) (K:Int) (cs:List Int) (desired:Int) : Formula :=
  compileFuel cs.length h K cs desired

/-- Finite BASE-language guard code. Tags0/1 are false/true,2 equality,
3 strict order,4 numeral lower bound,5 negation,6 conjunction,7 disjunction.
All names are the original occurrence indices; no new head-valued input. -/
abbrev Instruction:=Nat×Nat×Nat

def encode : Formula→List Instruction
  | .truth => [(1,0,0)] | .falsity => [(0,0,0)]
  | .eq i j => [(2,i,j)] | .lt i j => [(3,i,j)] | .bound c i => [(4,c,i)]
  | .neg p => encode p++[(5,0,0)]
  | .conj p q => encode p++encode q++[(6,0,0)]
  | .disj p q => encode p++encode q++[(7,0,0)]

noncomputable def compileCode (h:Nat) (K:Int) (cs:List Int) (desired:Int) : List Instruction :=
  encode (compile h K cs desired)
end LogicLineages.OrdinalComparison.LayeredComparison.CommonHeadCompiler
