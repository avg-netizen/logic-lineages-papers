module
public import LogicLineages.OrdinalComparison.GroundCompiledEqualityProof
public import LogicLineages.OrdinalComparison.WWOriginalInputFrontendComputability
public import LogicLineages.OrdinalComparison.WWDefaultSourceAssignmentSemanticProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.GroundSourceEquality
open Source Source.ForwardTranslation Source.OrdinalSyntax

attribute [local irreducible] Phi actualCollapse encodedMultivariateIdentity

theorem source_code_computable :
    Computable (fun p : Nat × Nat × Nat => sourceEqualityCode p.1 p.2.1 p.2.2) := by
  have hq : Primrec (fun p : Nat × Nat × Nat => (p.1,false,p.2.1,p.2.2)) :=
    Primrec.fst.pair ((Primrec.const false).pair Primrec.snd)
  have hs := (OriginalInput.compileSyntaxPrimitiveRecursive.comp hq).to_comp
  have hn : Computable₂ (fun _ : Nat × Nat × Nat => fun q : EncodedQuery =>
      queryEqualityFlag (normalizeQuerySyntaxCode q)) :=
    query_flag_computable.comp (querySyntaxNormalizationPrimitiveRecursive.to_comp.comp Computable.snd)
  exact Computable.option_getD (Computable.option_map hs hn) (Computable.const false)

private theorem context_codes (Γ : List Ty) (hΓ : ∀ σ ∈ Γ, σ=Ty.ground) :
    Γ.map SyntaxCode.typeCode=List.replicate Γ.length 0 := by
  induction Γ with
  | nil => rfl
  | cons σ Γ ih =>
    have he := hΓ σ (by simp)
    have hr : ∀ τ ∈ Γ, τ=Ty.ground := fun τ hτ => hΓ τ (by simp [hτ])
    simp only [List.map_cons,List.length_cons,List.replicate_succ,he,SyntaxCode.typeCode,ih hr]

private theorem source_compilation (Γ : List Ty) (hΓ : ∀ σ ∈ Γ, σ=Ty.ground)
    (τ υ : Ty) (a : OriginalTerm Γ τ) (b : OriginalTerm Γ υ)
    (av : OrdinalVector Γ τ.level) (bv : OrdinalVector Γ υ.level)
    (ac : CompiledVector (OrdinalComponent Γ) τ.level)
    (bc : CompiledVector (OrdinalComponent Γ) υ.level)
    (ha : AdmissibleAssignment.assignment defaultPolicy a=some av)
    (hb : AdmissibleAssignment.assignment defaultPolicy b=some bv)
    (hca : compileVector av=some ac) (hcb : compileVector bv=some bc) :
    sourceEqualityCode Γ.length (SyntaxCode.encodeTerm a) (SyntaxCode.encodeTerm b)=
      queryEqualityFlag (compiledQueryCode
        (fun c => SourceTypedPorts.variableIndex c.2.1) false ac bc) := by
  have hna := DefaultSourceAssignment.Proof.assignmentCorrect Γ τ a
  have hnb := DefaultSourceAssignment.Proof.assignmentCorrect Γ υ b
  rw [ha,context_codes Γ hΓ] at hna
  rw [hb,context_codes Γ hΓ] at hnb
  simp only [Option.map_some] at hna hnb
  have hva := ordinalSyntaxVectorCompilerCorrect Γ τ.level av
  have hvb := ordinalSyntaxVectorCompilerCorrect Γ υ.level bv
  rw [hca] at hva
  rw [hcb] at hvb
  simp only [Option.map_some] at hva hvb
  have hs : OriginalInput.compileSyntax
      (Γ.length,false,SyntaxCode.encodeTerm a,SyntaxCode.encodeTerm b)=
      some (compiledQuerySyntaxCode
        (fun c => SourceTypedPorts.variableIndex c.2.1) false ac bc) := by
    simp [OriginalInput.compileSyntax,hna,hnb,hva,hvb,compiledQuerySyntaxCode]
  simp only [sourceEqualityCode,hs,Option.map_some,Option.getD_some]
  exact congrArg queryEqualityFlag (querySyntaxNormalizationCorrect
    (OrdinalComponent Γ) τ.level υ.level
    (fun c => SourceTypedPorts.variableIndex c.2.1) false ac bc)

theorem full_equality : Targets.FullOriginalGroundEquality := by
  refine ⟨source_code_computable,?_⟩
  intro Γ hΓ τ υ a b
  obtain ⟨av,ha,ac,hca,_⟩ := actualSourceVectorCompilation Γ hΓ τ defaultPolicy a
  obtain ⟨bv,hb,bc,hcb,_⟩ := actualSourceVectorCompilation Γ hΓ υ defaultPolicy b
  rw [source_compilation Γ hΓ τ υ a b av bv ac bc ha hb hca hcb,
    compiled.2 Γ hΓ τ.level υ.level av bv ac bc hca hcb]
  constructor
  · intro h
    exact ⟨av,bv,ha,hb,h⟩
  · rintro ⟨av',bv',ha',hb',h⟩
    have ea : av=av' := Option.some.inj (ha.symm.trans ha')
    have eb : bv=bv' := Option.some.inj (hb.symm.trans hb')
    subst av'
    subst bv'
    exact h

end LogicLineages.OrdinalComparison.GroundSourceEquality
