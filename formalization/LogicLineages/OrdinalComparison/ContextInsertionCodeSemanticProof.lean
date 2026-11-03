module
public import LogicLineages.OrdinalComparison.ContextInsertionCodeTargets
public import LogicLineages.OrdinalComparison.WWOrdinalSyntaxHeadProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ContextInsertionCode.Proof
open SyntaxCode

private theorem mod_tag (a tag : Nat) (h : tag<8) : (8*a+tag)%8=tag := by omega
private theorem div_tag (a tag : Nat) (h : tag<8) : (8*a+tag)/8=a := by omega

private theorem index_step (depth count i : Nat) :
    indexCode (depth+1) count (i+1) = indexCode depth count i+1 := by
  by_cases h : i<depth <;> simp [indexCode,h] <;> omega

private theorem index_shift {Γ σ} (Δ : List Ty) (x : Variable Γ σ) :
    SourceTypedPorts.variableIndex (SourceTypedPorts.shiftVariable Δ x) = SourceTypedPorts.variableIndex x+Δ.length := by
  induction Δ with
  | nil => simp [SourceTypedPorts.shiftVariable]
  | cons τ Δ ih => simp [SourceTypedPorts.shiftVariable,SourceTypedPorts.variableIndex,ih,Nat.add_assoc]

theorem insertion_index (Θ Δ Γ : List Ty) {σ} (x : Variable (Θ++Γ) σ) :
    SourceTypedPorts.variableIndex (insertion Θ Δ Γ x) =
      indexCode Θ.length Δ.length (SourceTypedPorts.variableIndex x) := by
  induction Θ with
  | nil => simpa [insertion,HeterogeneousUnaryAssembly.prefixLift,indexCode] using index_shift Δ x
  | cons τ Θ ih =>
    cases x with
    | here => simp [insertion,HeterogeneousUnaryAssembly.prefixLift,Renaming.lift,SourceTypedPorts.variableIndex,indexCode]
    | there x =>
      change SourceTypedPorts.variableIndex (insertion Θ Δ Γ x)+1 = indexCode (Θ.length+1) Δ.length (SourceTypedPorts.variableIndex x+1)
      rw [ih,index_step]

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

theorem exactSourceInsertion : Targets.ExactSourceInsertion := by
  intro Θ Δ Γ τ t
  rw [encodeTerm,raw_correct,encodeTerm,erase_rename _ _ _ (insertion_index Θ Δ Γ) t]

private theorem ordinal_leaf (depth count i j : Nat) :
    ordinalLeaf depth count (8*Nat.pair i j+3) = 8*Nat.pair (indexCode depth count i) j+3 := by
  simp [ordinalLeaf,mod_tag _ 3 (by decide),div_tag _ 3 (by decide)]

private theorem ordinal_correct (Θ Δ Γ : List Ty) (q : OrdinalExpression (Θ++Γ)) :
    ordinalCode Θ.length Δ.length (OrdinalSyntax.typedCode q) =
      OrdinalSyntax.typedCode (ordinalExpressionRename (insertion Θ Δ Γ) q) := by
  unfold ordinalCode OrdinalSyntax.typedCode
  rw [OrdinalSyntax.ordinalSyntaxFoldCorrect]
  induction q with
  | var c =>
    rcases c with ⟨σ,x,j⟩
    simp [OrdinalSyntax.termFold,OrdinalSyntax.componentCode,ordinal_leaf,
      ordinalExpressionRename,ordinalComponentRename,OrdinalSyntax.code,
      ComputabilityKnowledge.WWOrdinalTermSemantics.substitute,insertion_index]
  | zero => rfl
  | one => rfl
  | omega => rfl
  | add a b iha ihb =>
    simp [OrdinalSyntax.termFold,iha,ihb,ordinalExpressionRename,
      ComputabilityKnowledge.WWOrdinalTermSemantics.substitute,OrdinalSyntax.code] at *
  | emul a b iha ihb =>
    simp [OrdinalSyntax.termFold,iha,ihb,ordinalExpressionRename,
      ComputabilityKnowledge.WWOrdinalTermSemantics.substitute,OrdinalSyntax.code] at *
  | collapse a b iha ihb =>
    simp [OrdinalSyntax.termFold,iha,ihb,ordinalExpressionRename,
      ComputabilityKnowledge.WWOrdinalTermSemantics.substitute,OrdinalSyntax.code] at *

theorem exactOrdinalVector : Targets.ExactOrdinalVector := by
  refine ⟨ordinal_correct,?_⟩
  intro Θ Δ Γ m v
  simp only [vectorCode,OrdinalSyntax.vectorCode,List.map_ofFn]
  apply congrArg List.ofFn
  funext j
  exact ordinal_correct Θ Δ Γ (v j)
end LogicLineages.OrdinalComparison.Source.ContextInsertionCode.Proof
