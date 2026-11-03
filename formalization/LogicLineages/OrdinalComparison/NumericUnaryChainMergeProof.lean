module
public import LogicLineages.OrdinalComparison.NumericUnaryChainTargets
public import LogicLineages.OrdinalComparison.ContextInsertionCodeProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.NumericUnaryChain.Proof
open SyntaxCode ContextInsertionCode HeterogeneousUnaryAssembly

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

private theorem ordinal_leaf (depth count i j : Nat) :
    ordinalLeaf depth count (8*Nat.pair i j+3) = 8*Nat.pair (indexCode depth count i) j+3 := by
  simp [ordinalLeaf,mod_tag _ 3 (by decide),div_tag _ 3 (by decide)]

private theorem ordinal_correct {Γ Δ} (depth count : Nat) (r : Renaming Γ Δ)
    (h : ∀ {σ} (x : Variable Γ σ), SourceTypedPorts.variableIndex (r x) = indexCode depth count (SourceTypedPorts.variableIndex x))
    (q : OrdinalExpression Γ) :
    ordinalCode depth count (OrdinalSyntax.typedCode q) =
      OrdinalSyntax.typedCode (ordinalExpressionRename r q) := by
  unfold ordinalCode OrdinalSyntax.typedCode
  rw [OrdinalSyntax.ordinalSyntaxFoldCorrect]
  induction q with
  | var c =>
    rcases c with ⟨σ,x,j⟩
    simp [OrdinalSyntax.termFold,OrdinalSyntax.componentCode,ordinal_leaf,
      ordinalExpressionRename,ordinalComponentRename,OrdinalSyntax.code,
      ComputabilityKnowledge.WWOrdinalTermSemantics.substitute,h]
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


private theorem source_correct {Γ Δ τ} (depth count : Nat) (r : Renaming Γ Δ)
    (h : ∀ {σ} (x : Variable Γ σ), SourceTypedPorts.variableIndex (r x) = indexCode depth count (SourceTypedPorts.variableIndex x))
    (t : OriginalTerm Γ τ) : sourceCode depth count (encodeTerm t) = encodeTerm (t.rename r) := by
  rw [encodeTerm,raw_correct,encodeTerm,erase_rename _ _ _ h t]

private theorem pair_correct {Γ Δ} (depth count : Nat) (r : Renaming Γ Δ)
    (h : ∀ {σ} (x : Variable Γ σ), SourceTypedPorts.variableIndex (r x) = indexCode depth count (SourceTypedPorts.variableIndex x))
    (p : OriginalTerm Γ (Ty.curriedGround 1) × OrdinalVector Γ 1) :
    shiftPair depth count (pairCode p) = pairCode (p.1.rename r,SourceRenaming.renameVector r p.2) := by
  apply Prod.ext
  · exact source_correct depth count r h p.1
  · change ContextInsertionCode.vectorCode depth count (OrdinalSyntax.vectorCode p.2) = _
    simp only [pairCode,ContextInsertionCode.vectorCode,OrdinalSyntax.vectorCode,List.map_ofFn]
    apply congrArg List.ofFn
    funext j
    exact ordinal_correct depth count r h (p.2 j)

private theorem base_index {Γ} (ops : List (Operator Γ)) {σ} (x : Variable Γ σ) :
    SourceTypedPorts.variableIndex (baseMap ops x) =
      SourceTypedPorts.variableIndex x+(ops.map (fun op => op.privateContext.length)).sum := by
  induction ops with
  | nil => rfl
  | cons op ops ih =>
    calc
      _ = SourceTypedPorts.variableIndex (baseMap ops x)+op.privateContext.length :=
        index_shift op.privateContext (baseMap ops x)
      _ = _ := by
        rw [ih]
        simp only [List.map_cons,List.sum_cons]
        omega

private theorem prefix_index {Γ Δ} (r : Renaming Γ Δ) (count : Nat)
    (h : ∀ {σ} (x : Variable Γ σ), SourceTypedPorts.variableIndex (r x) = SourceTypedPorts.variableIndex x+count)
    (Θ : List Ty) {σ} (x : Variable (Θ++Γ) σ) :
    SourceTypedPorts.variableIndex (prefixLift r Θ x) = indexCode Θ.length count (SourceTypedPorts.variableIndex x) := by
  induction Θ with
  | nil => simpa [prefixLift,indexCode] using h x
  | cons τ Θ ih =>
    cases x with
    | here => simp [prefixLift,Renaming.lift,SourceTypedPorts.variableIndex,indexCode]
    | there x =>
      change SourceTypedPorts.variableIndex (prefixLift r Θ x)+1 = indexCode (Θ.length+1) count (SourceTypedPorts.variableIndex x+1)
      rw [ih,index_step]

theorem exactMergedPayloads : Targets.ExactMergedPayloads := by
  intro Γ ops
  induction ops with
  | nil => exact ⟨rfl,rfl,rfl⟩
  | cons op ops ih =>
    refine ⟨?_,?_,?_⟩
    · change op.privateContext.map typeCode ++ contextCode (Γ.map typeCode) (ops.map operatorCode) = _
      rw [ih.1]
      exact List.map_append.symm
    · simp only [List.map_cons,operatorCode,mergeData,List.length_map,ih.2.1,List.sum_cons]
    · simp only [List.map_cons,operatorCode,mergeData,List.length_map,ih.2.1,ih.2.2,merged,List.map_cons,List.map_map]
      apply congrArg₂ List.cons
      · exact pair_correct op.privateContext.length (ops.map (fun op => op.privateContext.length)).sum
          (headMap op ops) (prefix_index (baseMap ops) _ (base_index ops) op.privateContext) (op.term,op.vector)
      · apply List.map_congr_left
        intro p hp
        exact pair_correct 0 op.privateContext.length (SourceTypedPorts.shiftVariable op.privateContext)
          (fun x => by simpa [indexCode] using index_shift op.privateContext x) p
end LogicLineages.OrdinalComparison.Source.NumericUnaryChain.Proof
