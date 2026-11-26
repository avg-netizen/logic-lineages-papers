module
public import LogicLineages.StandardControlCurrent.PolicySourceEqualityTargets
public import LogicLineages.StandardControlCurrent.PolicyAssignmentSyntaxProof
public import LogicLineages.StandardControlCurrent.DefaultSourceDomainProof
public import LogicLineages.OrdinalComparison.GroundSourceEqualityProof
@[expose] public section
namespace LogicLineages.StandardControlCurrent.PolicySourceEqualityProof
open OrdinalComparison Source Source.ForwardTranslation Source.OrdinalSyntax Source.OriginalDomain
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics
attribute [local irreducible] Phi actualCollapse encodedMultivariateIdentity
theorem context_codes (Γ : List Ty) (hΓ : ∀ σ ∈ Γ, σ=Ty.ground) :
    Γ.map SyntaxCode.typeCode=List.replicate Γ.length 0 := by
  induction Γ with
  | nil => rfl
  | cons σ Γ ih =>
    have he := hΓ σ (by simp)
    have hr : ∀ τ ∈ Γ, τ=Ty.ground := fun τ hτ => hΓ τ (by simp [hτ])
    simp only [List.map_cons,List.length_cons,List.replicate_succ,he,SyntaxCode.typeCode,ih hr]

theorem source_compilation (p : AdmissibleSum.Policy) (Γ : List Ty) (hΓ : ∀ σ ∈ Γ, σ=Ty.ground)
    (τ υ : Ty) (a : OriginalTerm Γ τ) (b : OriginalTerm Γ υ)
    (av : OrdinalVector Γ τ.level) (bv : OrdinalVector Γ υ.level)
    (ac : CompiledVector (OrdinalComponent Γ) τ.level)
    (bc : CompiledVector (OrdinalComponent Γ) υ.level)
    (ha : AdmissibleAssignment.assignment p a=some av)
    (hb : AdmissibleAssignment.assignment p b=some bv)
    (hca : compileVector av=some ac) (hcb : compileVector bv=some bc) :
    PolicySourceEquality.equalityCode p Γ.length (SyntaxCode.encodeTerm a) (SyntaxCode.encodeTerm b)=
      GroundSourceEquality.queryEqualityFlag (compiledQueryCode
        (fun c => SourceTypedPorts.variableIndex c.2.1) false ac bc) := by
  have hna := PolicyAssignmentSyntaxProof.literal p Γ τ a
  have hnb := PolicyAssignmentSyntaxProof.literal p Γ υ b
  rw [ha,context_codes Γ hΓ] at hna
  rw [hb,context_codes Γ hΓ] at hnb
  simp only [Option.map_some] at hna hnb
  have hva := ordinalSyntaxVectorCompilerCorrect Γ τ.level av
  have hvb := ordinalSyntaxVectorCompilerCorrect Γ υ.level bv
  rw [hca] at hva
  rw [hcb] at hvb
  simp only [Option.map_some] at hva hvb
  have hs : PolicySourceEquality.compileSyntax p Γ.length (SyntaxCode.encodeTerm a) (SyntaxCode.encodeTerm b)=
      some (compiledQuerySyntaxCode
        (fun c => SourceTypedPorts.variableIndex c.2.1) false ac bc) := by
    simp [PolicySourceEquality.compileSyntax,hna,hnb,hva,hvb,compiledQuerySyntaxCode]
  simp only [PolicySourceEquality.equalityCode,hs,Option.map_some,Option.getD_some]
  exact congrArg GroundSourceEquality.queryEqualityFlag (querySyntaxNormalizationCorrect
    (OrdinalComponent Γ) τ.level υ.level
    (fun c => SourceTypedPorts.variableIndex c.2.1) false ac bc)


private theorem vector_calibration {Γ : List Ty} {n : Nat} (v : OrdinalVector Γ n)
    (s : AdmissibleSubstitution Γ) (ρ : OrdinalComponent Γ → Nat)
    (hρ : ∀ c, valuation s c=(ρ c : Ordinal)) (j : Nat) :
    PolicySourceEquality.vectorAt v s j = sourceVectorAtValue v ρ j := by
  have he : valuation s = fun c => (ρ c : Ordinal) := funext hρ
  simp only [PolicySourceEquality.vectorAt,sourceVectorAtValue,ordinalVectorAt]
  split <;> simp only [expressionValue,he,denote]

theorem typed : PolicySourceEqualityTargets.TypedEquality := by
  intro p Γ hΓ τ υ a b
  obtain ⟨av,ha,ac,hca,_⟩ := actualSourceVectorCompilation Γ hΓ τ p a
  obtain ⟨bv,hb,bc,hcb,_⟩ := actualSourceVectorCompilation Γ hΓ υ p b
  rw [source_compilation p Γ hΓ τ υ a b av bv ac bc ha hb hca hcb,
    GroundSourceEquality.compiled.2 Γ hΓ τ.level υ.level av bv ac bc hca hcb]
  constructor
  · intro h
    refine ⟨av,bv,ha,hb,?_⟩
    intro s j
    obtain ⟨ρ,hp,hv⟩ := DefaultSourceDomainProof.domain.2 Γ hΓ s
    rw [vector_calibration av s ρ hv j,vector_calibration bv s ρ hv j]
    exact h ρ hp j
  · rintro ⟨av',bv',ha',hb',h⟩
    have ea : av=av' := Option.some.inj (ha.symm.trans ha')
    have eb : bv=bv' := Option.some.inj (hb.symm.trans hb')
    subst av'; subst bv'
    intro ρ hp j
    obtain ⟨s,hv⟩ := DefaultSourceDomainProof.domain.1 Γ hΓ ρ hp
    rw [←vector_calibration av s ρ hv j,←vector_calibration bv s ρ hv j]
    exact h s j

theorem raw : PolicySourceEqualityTargets.RawEquality := by
  intro p d n m
  let Γ := List.replicate d Ty.ground
  have hg : ∀ σ ∈ Γ, σ=Ty.ground := by simp [Γ]
  have hl : Γ.length=d := by simp [Γ]
  constructor
  · intro h
    have hs : ∃ q, PolicySourceEquality.compileSyntax p d n m=some q := by
      cases hc : PolicySourceEquality.compileSyntax p d n m with
      | none => simp [PolicySourceEquality.equalityCode,hc] at h
      | some q => exact ⟨q,rfl⟩
    obtain ⟨q,hq⟩ := hs
    obtain ⟨av,ha,bv,hb⟩ : ∃ av, PolicyAssignment.assignmentCode p (List.replicate d 0) n=some av ∧
        ∃ bv, PolicyAssignment.assignmentCode p (List.replicate d 0) m=some bv := by
      cases ha : PolicyAssignment.assignmentCode p (List.replicate d 0) n with
      | none => simp [PolicySourceEquality.compileSyntax,ha] at hq
      | some av =>
        cases hb : PolicyAssignment.assignmentCode p (List.replicate d 0) m with
        | none => simp [PolicySourceEquality.compileSyntax,ha,hb] at hq
        | some bv => exact ⟨av,rfl,bv,rfl⟩
    have hac : PolicyAssignment.assignmentCode p (Γ.map SyntaxCode.typeCode) n=some av := by
      rw [context_codes Γ hg,hl]; exact ha
    have hbc : PolicyAssignment.assignmentCode p (Γ.map SyntaxCode.typeCode) m=some bv := by
      rw [context_codes Γ hg,hl]; exact hb
    obtain ⟨τ,a,va,ea,hva,_⟩ := (PolicyAssignmentSyntaxProof.sourceExact p Γ n av).mp hac
    obtain ⟨υ,b,vb,eb,hvb,_⟩ := (PolicyAssignmentSyntaxProof.sourceExact p Γ m bv).mp hbc
    have ht := (typed p Γ hg τ υ a b).mp (by simpa only [hl,ea,eb] using h)
    obtain ⟨va',vb',hva',hvb',he⟩ := ht
    exact ⟨τ,υ,a,b,va',vb',ea,eb,hva',hvb',he⟩
  · rintro ⟨τ,υ,a,b,av,bv,ea,eb,ha,hb,he⟩
    have ht := (typed p Γ hg τ υ a b).mpr ⟨av,bv,ha,hb,he⟩
    simpa only [hl,ea,eb] using ht
end LogicLineages.StandardControlCurrent.PolicySourceEqualityProof
