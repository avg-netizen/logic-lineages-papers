module
public import LogicLineages.OrdinalComparison.SourcePlanInsertionCodeRecursionProof
public import LogicLineages.OrdinalComparison.SourcePlanSpineCodeCalibrationProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourcePlanInsertionCode.Proof
open SyntaxCode ContextInsertionCode ExistentialPlan PrimitiveLowering SourcePrimitiveForestCode SourcePlanSpineCode
private theorem mod_tag (a tag : Nat) (h : tag<8) : (8*a+tag)%8=tag := by omega
private theorem div_tag (a tag : Nat) (h : tag<8) : (8*a+tag)/8=a := by omega
private theorem index_step (depth count i : Nat) : indexCode (depth+1) count (i+1)=indexCode depth count i+1 := by
  by_cases h : i<depth <;> simp [indexCode,h] <;> omega
private def mapRaw (depth count : Nat) : Raw → Raw
  | .var i => .var (indexCode depth count i)
  | .zero => .zero
  | .succ => .succ
  | .caseC τ => .caseC τ
  | .recC τ => .recC τ
  | .app f a => .app (mapRaw depth count f) (mapRaw depth count a)
  | .lam σ b => .lam σ (mapRaw (depth+1) count b)

private theorem raw_correct (depth count : Nat) (t : Raw) :
    sourceCode depth count (code t) = code (mapRaw depth count t) := by
  induction t generalizing depth with
  | var i => rw [code,sourceCode];simp [mapRaw,code]
  | zero => rw [code,sourceCode];simp [mapRaw,code]
  | succ => rw [code,sourceCode];simp [mapRaw,code]
  | caseC τ => rw [code,sourceCode];simp [mod_tag _ 3 (by decide),mapRaw,code]
  | recC τ => rw [code,sourceCode];simp [mod_tag _ 4 (by decide),mapRaw,code]
  | app f a ihf iha =>
    rw [code,sourceCode]
    simp [mod_tag _ 5 (by decide),div_tag _ 5 (by decide),ihf,iha,mapRaw,code]
  | lam σ b ih =>
    rw [code,sourceCode]
    simp [mod_tag _ 6 (by decide),div_tag _ 6 (by decide),ih,mapRaw,code]

private theorem lift_index {Γ Δ τ} {depth count : Nat} (r : Renaming Γ Δ)
    (h : ∀ {σ} (x : Variable Γ σ), SourceTypedPorts.variableIndex (r x) = indexCode depth count (SourceTypedPorts.variableIndex x)) :
    ∀ {σ} (x : Variable (τ::Γ) σ), SourceTypedPorts.variableIndex (Renaming.lift r x) =
      indexCode (depth+1) count (SourceTypedPorts.variableIndex x) := by
  intro σ x
  cases x with
  | here => simp [Renaming.lift,SourceTypedPorts.variableIndex,indexCode]
  | there x =>
    change SourceTypedPorts.variableIndex (r x)+1 = indexCode (depth+1) count (SourceTypedPorts.variableIndex x+1)
    rw [h,index_step]

private theorem erase_rename {Γ Δ τ} (depth count : Nat) (r : Renaming Γ Δ)
    (h : ∀ {σ} (x : Variable Γ σ), SourceTypedPorts.variableIndex (r x) = indexCode depth count (SourceTypedPorts.variableIndex x))
    (t : OriginalTerm Γ τ) : erase (t.rename r) = mapRaw depth count (erase t) := by
  induction t generalizing Δ depth with
  | var x => simp [Source.Term.rename,erase,mapRaw,h]
  | zeroC => rfl
  | succC => rfl
  | caseC σ => rfl
  | recC σ => rfl
  | app f a ihf iha => simp only [Source.Term.rename,erase,mapRaw,ihf _ r h,iha _ r h]
  | lam b ih =>
    simp only [Source.Term.rename,erase,mapRaw]
    rw [ih (depth+1) (Renaming.lift r) (lift_index r h)]
  | ranked s _ => nomatch s


private theorem source_rename {Γ Δ τ} (d k : Nat) (r : Renaming Γ Δ)
    (h : ∀ {σ} (x : Variable Γ σ),SourceTypedPorts.variableIndex (r x)=indexCode d k (SourceTypedPorts.variableIndex x))
    (t : OriginalTerm Γ τ) : sourceCode d k (encodeTerm t)=encodeTerm (t.rename r) := by
  rw [encodeTerm,raw_correct,encodeTerm,erase_rename d k r h t]

private theorem port_rename {Γ Δ} (d k : Nat) (r : Renaming Γ Δ)
    (h : ∀ {σ} (x : Variable Γ σ),SourceTypedPorts.variableIndex (r x)=indexCode d k (SourceTypedPorts.variableIndex x))
    (a : Port Γ) : portInsert d k (portNumber a)=portNumber (portRename r a) := by
  cases a with
  | zero => simp [portInsert,portNumber,portRename]
  | var x =>
    simp only [portNumber,portRename,h,indexCode,portInsert,Nat.add_sub_cancel]
    by_cases hx : SourceTypedPorts.variableIndex x<d <;> simp [hx] <;> omega

private theorem spine_rename {Γ Δ} (q : Plan Γ) (hq : ParametricExistentialPlan.Supported q)
    (d k : Nat) (r : Renaming Γ Δ)
    (h : ∀ {σ} (x : Variable Γ σ),SourceTypedPorts.variableIndex (r x)=indexCode d k (SourceTypedPorts.variableIndex x)) :
    insert d k (spine q)=spine (BinaryPlan.renamePlan r q) := by
  induction q generalizing Δ d with
  | done => rfl
  | @equation Γ a b q ih =>
    simp only [spine,BinaryPlan.renamePlan,insert_cons,instruction,ite_true,nextDepth,show (0:Nat)≠4 by decide,ite_false]
    rw [(ScopedDAG.Proof.renaming Γ Δ .ground r a).1,(ScopedDAG.Proof.renaming Γ Δ .ground r b).1,
      source_rename d k r h,source_rename d k r h,ih hq d r h]
  | gate g q ih =>
    have ht := ih hq.2 d r h
    cases g with
    | eq a b => simp [spine,BinaryPlan.renamePlan,gateInstruction,gateRename,insert_cons,instruction,nextDepth,port_rename d k r h,ht]
    | add a b c => simp [spine,BinaryPlan.renamePlan,gateInstruction,gateRename,insert_cons,instruction,nextDepth,port_rename d k r h,ht]
    | one a => simp [spine,BinaryPlan.renamePlan,gateInstruction,gateRename,insert_cons,instruction,nextDepth,port_rename d k r h,ht]
    | sort a b c e => exact False.elim hq.1
  | @existsGround Γ q ih =>
    simp only [spine,BinaryPlan.renamePlan,insert_cons,instruction,nextDepth,
      show (4:Nat)≠0 by decide,show (4:Nat)≠1 by decide,show (4:Nat)≠2 by decide,show (4:Nat)≠3 by decide,ite_false,ite_true]
    rw [ih hq (d+1) (Renaming.lift r) (lift_index r h)]

theorem exactSupportedInsertion : Targets.ExactSupportedInsertion := by
  intro Θ Δ Γ q hq
  exact spine_rename q hq Θ.length Δ.length (ContextInsertionCode.insertion Θ Δ Γ)
    (ContextInsertionCode.Proof.insertion_index Θ Δ Γ)
end LogicLineages.OrdinalComparison.Source.SourcePlanInsertionCode.Proof
