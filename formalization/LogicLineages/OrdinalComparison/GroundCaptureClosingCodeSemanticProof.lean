module
public import LogicLineages.OrdinalComparison.GroundCaptureClosingCodeTargets
public import LogicLineages.OrdinalComparison.WWGroundClosingCodeProof
public import LogicLineages.OrdinalComparison.WWOrdinalSyntaxHeadProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.GroundCaptureClosingCode.Proof
open GroundClosing SyntaxCode

private theorem mod_tag (a tag : Nat) (h : tag<8) : (8*a+tag)%8=tag := by omega
private theorem div_tag (a tag : Nat) (h : tag<8) : (8*a+tag)/8=a := by omega

private theorem lookup_type {Γ σ} (x : Variable Γ σ) :
    (Γ.map typeCode).getD (SourceTypedPorts.variableIndex x) 1 = typeCode σ := by
  induction x with
  | here => rfl
  | there x ih => simpa [SourceTypedPorts.variableIndex,List.getD] using ih

private theorem lookup_normal {Γ σ} (x : Variable Γ σ) :
    (Option.map typeCode Γ[SourceTypedPorts.variableIndex x]?).getD 1 = typeCode σ := by
  simpa [List.getD_eq_getElem?_getD] using lookup_type x

private def variableRaw (Γ : List Nat) (depth i : Nat) : Raw :=
  if i<depth then .var i else if Γ.getD (i-depth) 1=0 then .zero else .var i
private def mapRaw (Γ : List Nat) (depth : Nat) : Raw → Raw
  | .var i => variableRaw Γ depth i
  | .zero => .zero
  | .succ => .succ
  | .caseC τ => .caseC τ
  | .recC τ => .recC τ
  | .app f a => .app (mapRaw Γ depth f) (mapRaw Γ depth a)
  | .lam σ b => .lam σ (mapRaw Γ (depth+1) b)

private theorem raw_correct (Γ : List Nat) (depth : Nat) (t : Raw) :
    sourceCode Γ depth (code t) = code (mapRaw Γ depth t) := by
  induction t generalizing depth with
  | var i =>
    rw [code,sourceCode]
    simp only [Nat.mul_mod_right,Nat.mul_div_cancel_left i (by decide : 0<8),if_pos rfl]
    by_cases hi : i<depth <;> by_cases hz : Γ.getD (i-depth) 1=0 <;>
      simp only [variableCode,mapRaw,variableRaw,hi,hz,↓reduceIte,code]
  | zero => rw [code,sourceCode]; simp [mapRaw,code]
  | succ => rw [code,sourceCode]; simp [mapRaw,code]
  | caseC τ => rw [code,sourceCode]; simp [mod_tag _ 3 (by decide),mapRaw,code]
  | recC τ => rw [code,sourceCode]; simp [mod_tag _ 4 (by decide),mapRaw,code]
  | app f a ihf iha =>
    rw [code,sourceCode]
    simp [mod_tag _ 5 (by decide),div_tag _ 5 (by decide),ihf,iha,mapRaw,code]
  | lam σ b ih =>
    rw [code,sourceCode]
    simp [mod_tag _ 6 (by decide),div_tag _ 6 (by decide),ih,mapRaw,code]

private def Compatible {Γ Δ} (ctx : List Nat) (depth : Nat) (r : GroundMap Γ Δ) : Prop :=
  ∀ {σ} (x : Variable Γ σ), erase (Image.source (r x)) = variableRaw ctx depth (SourceTypedPorts.variableIndex x)

private def shiftRaw : Raw → Raw
  | .var i => .var (i+1)
  | q => q

private theorem variable_step (ctx : List Nat) (depth i : Nat) :
    variableRaw ctx (depth+1) (i+1) = shiftRaw (variableRaw ctx depth i) := by
  by_cases hi : i<depth <;> by_cases hz : ctx.getD (i-depth) 1=0 <;>
    simp only [variableRaw,Nat.add_lt_add_iff_right,Nat.add_sub_add_right,hi,hz,↓reduceIte,shiftRaw]

private theorem compatible_lift {Γ Δ τ} {ctx : List Nat} {depth : Nat}
    {r : GroundMap Γ Δ} (h : Compatible ctx depth r) :
    Compatible ctx (depth+1) (@GroundMap.lift Γ Δ τ r) := by
  intro σ x
  cases x with
  | here => simp [GroundMap.lift,Image.source,erase,variableRaw,SourceTypedPorts.variableIndex]
  | there x =>
    have hx := congrArg shiftRaw (h x)
    change erase ((@GroundMap.lift Γ Δ τ r _ (.there x)).source) =
      variableRaw ctx (depth+1) (SourceTypedPorts.variableIndex x+1)
    calc
      erase ((@GroundMap.lift Γ Δ τ r _ (.there x)).source) = shiftRaw (erase (r x).source) := by
        cases he : r x <;> simp [GroundMap.lift,he,Image.weaken,Image.source,erase,
          SourceTypedPorts.variableIndex,shiftRaw]
      _ = shiftRaw (variableRaw ctx depth (SourceTypedPorts.variableIndex x)) := hx
      _ = variableRaw ctx (depth+1) (SourceTypedPorts.variableIndex x+1) := (variable_step _ _ _).symm

private theorem map_substitute {Γ Δ τ} (ctx : List Nat) (depth : Nat)
    (r : GroundMap Γ Δ) (h : Compatible ctx depth r) (t : OriginalTerm Γ τ) :
    erase (t.substitute (GroundMap.source r)) = mapRaw ctx depth (erase t) := by
  induction t generalizing Δ depth with
  | var x => exact h x
  | zeroC => rfl
  | succC => rfl
  | caseC σ => rfl
  | recC σ => rfl
  | app f a ihf iha => simp only [Source.Term.substitute,erase,mapRaw,ihf _ r h,iha _ r h]
  | lam b ih =>
    simp only [Source.Term.substitute,← GroundClosingCode.Proof.source_lift,erase,mapRaw]
    rw [ih (depth+1) r.lift (compatible_lift h)]
  | ranked s _ => nomatch s

private theorem protected_compatible (Θ Γ : List Ty) :
    Compatible (Γ.map typeCode) Θ.length (protectedMap Θ Γ) := by
  induction Θ with
  | nil =>
    intro σ x
    cases σ <;> simp [protectedMap,UnaryCarrier.groundMap,Image.source,erase,variableRaw,
      lookup_type,lookup_normal,typeCode,arrowCode]
  | cons τ Θ ih => exact compatible_lift ih

theorem exactProtectedSource : Targets.ExactProtectedSource := by
  intro Θ Γ τ t
  rw [encodeTerm,raw_correct,encodeTerm,map_substitute _ _ _ (protected_compatible Θ Γ) t]

private theorem ordinal_leaf (Γ : List Nat) (i j : Nat) :
    ordinalLeaf Γ (8*Nat.pair i j+3) =
      if Γ.getD i 1=0 then 1 else 8*Nat.pair i j+3 := by
  simp [ordinalLeaf,mod_tag _ 3 (by decide),div_tag _ 3 (by decide)]

private theorem ordinal_correct (Γ : List Ty) (q : OrdinalExpression Γ) :
    ordinalCode (Γ.map typeCode) (OrdinalSyntax.typedCode q) =
      OrdinalSyntax.typedCode (GroundClosing.expression (UnaryCarrier.groundMap Γ) q) := by
  unfold ordinalCode OrdinalSyntax.typedCode
  rw [OrdinalSyntax.ordinalSyntaxFoldCorrect]
  induction q with
  | var c =>
    rcases c with ⟨σ,x,j⟩
    cases σ <;> simp [OrdinalSyntax.termFold,OrdinalSyntax.componentCode,ordinal_leaf,lookup_type,lookup_normal,
      typeCode,arrowCode,GroundClosing.expression,GroundClosing.component,UnaryCarrier.groundMap,
      OrdinalSyntax.code,ComputabilityKnowledge.WWOrdinalTermSemantics.substitute]
  | zero => rfl
  | one => rfl
  | omega => rfl
  | add a b iha ihb =>
    simp [OrdinalSyntax.termFold,iha,ihb,GroundClosing.expression,
      ComputabilityKnowledge.WWOrdinalTermSemantics.substitute,OrdinalSyntax.code] at *
  | emul a b iha ihb =>
    simp [OrdinalSyntax.termFold,iha,ihb,GroundClosing.expression,
      ComputabilityKnowledge.WWOrdinalTermSemantics.substitute,OrdinalSyntax.code] at *
  | collapse a b iha ihb =>
    simp [OrdinalSyntax.termFold,iha,ihb,GroundClosing.expression,
      ComputabilityKnowledge.WWOrdinalTermSemantics.substitute,OrdinalSyntax.code] at *

theorem exactOrdinalVector : Targets.ExactOrdinalVector := by
  refine ⟨ordinal_correct,?_⟩
  intro Γ m v
  simp only [vectorCode,OrdinalSyntax.vectorCode,List.map_ofFn]
  apply congrArg List.ofFn
  funext j
  exact ordinal_correct Γ (v j)
end LogicLineages.OrdinalComparison.Source.GroundCaptureClosingCode.Proof
