module
public import LogicLineages.OrdinalComparison.OneNameSourceScalarProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.OneNameSourceBoolean
open Source Source.ForwardTranslation Source.OrdinalSyntax

theorem atom_program_source {τ υ : Ty} (relation : OneInputOrderRelation)
    (a : OriginalTerm [Ty.ground] τ) (b : OriginalTerm [Ty.ground] υ)
    (av : OrdinalVector [Ty.ground] τ.level) (bv : OrdinalVector [Ty.ground] υ.level)
    (ac : CompiledVector (OrdinalComponent [Ty.ground]) τ.level)
    (bc : CompiledVector (OrdinalComponent [Ty.ground]) υ.level)
    (ha : AdmissibleAssignment.assignment defaultPolicy a=some av)
    (hb : AdmissibleAssignment.assignment defaultPolicy b=some bv)
    (hca : compileVector av=some ac) (hcb : compileVector bv=some bc) :
    encodedOneNameSourceAtomProgram (oneInputOrderRelationCode relation)
      (SyntaxCode.encodeTerm a) (SyntaxCode.encodeTerm b)=
        oneInputBooleanCompile (compiledAtomFormula relation ac bc) := by
  have hna := DefaultSourceAssignment.Proof.assignmentCorrect [Ty.ground] τ a
  have hnb := DefaultSourceAssignment.Proof.assignmentCorrect [Ty.ground] υ b
  rw [ha] at hna
  rw [hb] at hnb
  simp only [List.map_cons,List.map_nil,SyntaxCode.typeCode,Option.map_some] at hna hnb
  have hva := ordinalSyntaxVectorCompilerCorrect [Ty.ground] τ.level av
  have hvb := ordinalSyntaxVectorCompilerCorrect [Ty.ground] υ.level bv
  rw [hca] at hva
  rw [hcb] at hvb
  simp only [Option.map_some] at hva hvb
  have hs : OriginalInput.compileSyntax (1,false,SyntaxCode.encodeTerm a,SyntaxCode.encodeTerm b)=
      some (compiledQuerySyntaxCode (fun c => SourceTypedPorts.variableIndex c.2.1) false ac bc) := by
    simp [OriginalInput.compileSyntax,hna,hnb,hva,hvb,compiledQuerySyntaxCode]
  unfold encodedOneNameSourceAtomProgram
  rw [hs]
  dsimp only
  rw [querySyntaxNormalizationCorrect (OrdinalComponent [Ty.ground]) τ.level υ.level
    (fun c => SourceTypedPorts.variableIndex c.2.1) false ac bc]
  simp only [compiledAtomFormula,oneInputBooleanCompile,List.singleton_append,List.cons_append,List.nil_append,
    compiledQueryCode,CompiledVector.code,scalar_code]
  rfl

theorem atom_realization {τ υ : Ty} (relation : OneInputOrderRelation)
    (a : OriginalTerm [Ty.ground] τ) (b : OriginalTerm [Ty.ground] υ) :
    ∃ formula : OneInputBooleanExpr,oneInputBooleanValid formula ∧
      encodedOneNameSourceBooleanProgram (oneNameSourceBooleanCompile (.atom relation a b))=
        oneInputBooleanCompile formula ∧
      ∀ x : Nat,0<x → actualOneInputBooleanValue formula x=actualOneNameSourceBooleanValue (.atom relation a b) x := by
  have hΓ : ∀ σ∈[Ty.ground],σ=Ty.ground := by simp
  obtain ⟨av,ha,ac,hca,_⟩ := actualSourceVectorCompilation [Ty.ground] hΓ τ defaultPolicy a
  obtain ⟨bv,hb,bc,hcb,_⟩ := actualSourceVectorCompilation [Ty.ground] hΓ υ defaultPolicy b
  refine ⟨compiledAtomFormula relation ac bc,compiled_valid relation ac bc,?_,?_⟩
  · have hp : encodedOneNameSourceBooleanProgram (oneNameSourceBooleanCompile (.atom relation a b))=
        encodedOneNameSourceAtomProgram (oneInputOrderRelationCode relation)
          (SyntaxCode.encodeTerm a) (SyntaxCode.encodeTerm b) := by
      cases relation <;>
        simp [encodedOneNameSourceBooleanProgram,oneNameSourceBooleanCompile,oneInputOrderRelationCode]
    rw [hp]
    exact atom_program_source relation a b av bv ac bc ha hb hca hcb
  · intro x hx
    apply Bool.eq_iff_iff.mpr
    rw [compiled_point relation av bv ac bc hca hcb x]
    simp only [actualOneNameSourceBooleanValue,decide_eq_true_eq]
    change _ ↔ actualOneNameSourceAtom relation a b x
    constructor
    · intro h
      exact ⟨av,bv,ha,hb,h⟩
    · rintro ⟨av',bv',ha',hb',h⟩
      have hea : av=av' := Option.some.inj (ha.symm.trans ha')
      have heb : bv=bv' := Option.some.inj (hb.symm.trans hb')
      subst av' bv'
      exact h

theorem program_append (left right : List OneInputBooleanInstruction) :
    encodedOneNameSourceBooleanProgram (left++right)=
      encodedOneNameSourceBooleanProgram left++encodedOneNameSourceBooleanProgram right :=
  List.flatMap_append

theorem formula_realization (source : OneNameSourceBooleanExpr) :
    ∃ formula : OneInputBooleanExpr,oneInputBooleanValid formula ∧
      encodedOneNameSourceBooleanProgram (oneNameSourceBooleanCompile source)=oneInputBooleanCompile formula ∧
      ∀ x : Nat,0<x → actualOneInputBooleanValue formula x=actualOneNameSourceBooleanValue source x := by
  induction source with
  | truth value =>
    refine ⟨.truth value,True.intro,?_,fun x hx => rfl⟩
    cases value <;> rfl
  | atom relation a b => exact atom_realization relation a b
  | neg source ih =>
    obtain ⟨formula,hValid,hCode,hValue⟩ := ih
    refine ⟨.neg formula,hValid,?_,?_⟩
    · change encodedOneNameSourceBooleanProgram (oneNameSourceBooleanCompile source++[(5,0,0)])=_
      rw [program_append,hCode]
      rfl
    · intro x hx
      exact congrArg Bool.not (hValue x hx)
  | conj left right ihL ihR =>
    obtain ⟨E,hE,hEc,hEv⟩ := ihL
    obtain ⟨F,hF,hFc,hFv⟩ := ihR
    refine ⟨.conj E F,⟨hE,hF⟩,?_,?_⟩
    · change encodedOneNameSourceBooleanProgram
        (oneNameSourceBooleanCompile left++oneNameSourceBooleanCompile right++[(6,0,0)])=_
      rw [program_append,program_append,hEc,hFc]
      rfl
    · intro x hx
      exact congrArg₂ Bool.and (hEv x hx) (hFv x hx)
  | disj left right ihL ihR =>
    obtain ⟨E,hE,hEc,hEv⟩ := ihL
    obtain ⟨F,hF,hFc,hFv⟩ := ihR
    refine ⟨.disj E F,⟨hE,hF⟩,?_,?_⟩
    · change encodedOneNameSourceBooleanProgram
        (oneNameSourceBooleanCompile left++oneNameSourceBooleanCompile right++[(7,0,0)])=_
      rw [program_append,program_append,hEc,hFc]
      rfl
    · intro x hx
      exact congrArg₂ Bool.or (hEv x hx) (hFv x hx)

end LogicLineages.OrdinalComparison.OneNameSourceBoolean
