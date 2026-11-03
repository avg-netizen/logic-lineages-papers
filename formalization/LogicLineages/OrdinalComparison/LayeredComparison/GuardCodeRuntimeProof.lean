module
public import LogicLineages.OrdinalComparison.LayeredComparison.GuardCodeRuntimeTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.CommonHeadCodeInterfacesProof
public import LogicLineages.OrdinalComparison.LayeredComparison.CommonHeadCompilerProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.GuardCodeRuntime.Proof
open CommonHeadCompiler CommonHeadLargeGuards CommonHeadLargeRow

private theorem run_append (ν:Nat→Nat) (xs ys:List Instruction) (stack:List Bool):
    run ν (xs++ys) stack=run ν ys (run ν xs stack):=List.foldl_append

private theorem run_encode (p:Formula) (ν:Nat→Nat) (stack:List Bool):
    run ν (encode p) stack=boolValue ν p::stack:=by
  induction p generalizing stack with
  | truth=>simp [encode,run,step,boolValue]
  | falsity=>simp [encode,run,step,boolValue]
  | eq i j=>simp [encode,run,step,boolValue]
  | lt i j=>simp [encode,run,step,boolValue]
  | bound c i=>simp [encode,run,step,boolValue]
  | neg p ih=>
    simp only [encode,run_append,ih]
    simp [run,step,boolValue]
  | conj p q ihp ihq=>
    simp only [encode,run_append,ihp,ihq]
    simp [run,step,boolValue]
  | disj p q ihp ihq=>
    simp only [encode,run_append,ihp,ihq]
    simp [run,step,boolValue]

private theorem variables_append (xs ys:List Instruction):
    codeVariables (xs++ys)=codeVariables xs++codeVariables ys:=by
  simp [codeVariables,List.flatMap_append]
private theorem variables_encode (p:Formula):codeVariables (encode p)=p.variables:=by
  induction p with
  | truth=>simp [encode,codeVariables,Formula.variables]
  | falsity=>simp [encode,codeVariables,Formula.variables]
  | eq i j=>simp [encode,codeVariables,Formula.variables]
  | lt i j=>simp [encode,codeVariables,Formula.variables]
  | bound c i=>simp [encode,codeVariables,Formula.variables]
  | neg p ih=>
    simp only [encode,variables_append,ih,Formula.variables]
    simp [codeVariables]
  | conj p q ihp ihq=>
    simp only [encode,variables_append,ihp,ihq,Formula.variables]
    simp [codeVariables]
  | disj p q ihp ihq=>
    simp only [encode,variables_append,ihp,ihq,Formula.variables]
    simp [codeVariables]
private theorem bool_exact (p:Formula) (ν:Nat→Nat):boolValue ν p=true↔p.eval ν:=by
  induction p with
  | truth=>simp [boolValue,Formula.eval]
  | falsity=>simp [boolValue,Formula.eval]
  | eq i j=>simp [boolValue,Formula.eval]
  | lt i j=>simp [boolValue,Formula.eval]
  | bound c i=>simp [boolValue,Formula.eval]
  | neg p ih=>
    change (Bool.not (boolValue ν p)=true)↔¬p.eval ν
    rw [←ih]
    cases boolValue ν p <;> decide
  | conj p q ihp ihq=>simp [boolValue,Formula.eval,ihp,ihq]
  | disj p q ihp ihq=>simp [boolValue,Formula.eval,ihp,ihq]

theorem literalEncoding : Targets.ExactLiteralEncoding:=by
  intro p
  exact ⟨run_encode p,variables_encode p,bool_exact p⟩

theorem completeRowCode : Targets.CompleteRowCode:=by
  refine ⟨CommonHeadCode.Program.allCodeEffectivity,?_,?_⟩
  · intro rho hlim K cs desired ν hg
    unfold evaluate compileCode
    rw [run_encode]
    simp only [List.headD_cons]
    exact (bool_exact _ ν).trans (CommonHeadCompiler.Proof.exactSourceRow rho hlim K cs desired ν hg)
  · intro h K cs desired i hi
    rw [compileCode,variables_encode] at hi
    exact CommonHeadCompiler.Proof.originalSupport cs.length h K cs desired i hi
end LogicLineages.OrdinalComparison.LayeredComparison.GuardCodeRuntime.Proof
