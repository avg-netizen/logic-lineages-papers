module
public import LogicLineages.StandardControlCurrent.PolicyFiniteCheckPrograms
@[expose] public section
namespace LogicLineages.StandardControlCurrent.PolicyFiniteProof
open OrdinalComparison Source Source.ForwardTranslation Source.SourceClasses Source.AdmissibleSum
open LevelTwoCounterexample

theorem finite_compiled {Γ : List Ty} {τ : Ty} {p : Policy} {t : OriginalTerm Γ τ}
    (v : OrdinalVector Γ τ.level) (c : CompiledVector (OrdinalComponent Γ) τ.level)
    (hv : AdmissibleAssignment.assignment p t=some v) (hc : compileVector v=some c) :
    PolicyFinite.FiniteSource p t ↔ PolicyFinite.FiniteScalar c.scalar := by
  have hs := LevelTwoDecisionCompletion.MetadataProof.compiled_scalar v c hc
  constructor
  · rintro ⟨v',s,hv',hs',hf⟩
    have ev : v'=v := Option.some.inj (hv'.symm.trans hv)
    subst v'
    have es : s=c.scalar := Option.some.inj (hs'.symm.trans hs)
    simpa only [es] using hf
  · intro hf; exact ⟨v,c.scalar,hv,hs,hf⟩

theorem pair_interface (p : Policy) (d n m : Nat) :
    PolicySourceEquality.compileSyntax p d n m=(do
      let a ← PolicySourceInterface.compile p d n
      let b ← PolicySourceInterface.compile p d m
      pure (false,a,b)) := by
  unfold PolicySourceEquality.compileSyntax PolicySourceInterface.compile
  cases ha : PolicyAssignment.assignmentCode p (List.replicate d 0) n with
  | none => rfl
  | some av =>
    cases hb : PolicyAssignment.assignmentCode p (List.replicate d 0) m with
    | none =>
      simp only [bind,pure,Option.bind_some,Option.bind_none]
      cases OrdinalSyntax.compileVectorCode av <;> rfl
    | some bv =>
      simp only [bind,pure,Option.bind_some,Option.bind_none]
      cases OrdinalSyntax.compileVectorCode av <;> cases OrdinalSyntax.compileVectorCode bv <;> rfl

theorem typed_accepts (p : Policy) (Γ : List Ty) (hΓ : ∀ σ ∈ Γ,σ=Ty.ground)
    (τ υ : Ty) (a : OriginalTerm Γ τ) (b : OriginalTerm Γ υ) (mode : Nat) :
    PolicyFinite.accepts p (Γ.length,mode,SyntaxCode.encodeTerm a,SyntaxCode.encodeTerm b)=true ↔
      PolicyFinite.FiniteSource p a ∧ PolicyFinite.FiniteSource p b := by
  obtain ⟨av,ha,ac,hac,_⟩ := actualSourceVectorCompilation Γ hΓ τ p a
  obtain ⟨bv,hb,bc,hbc,_⟩ := actualSourceVectorCompilation Γ hΓ υ p b
  unfold PolicyFinite.accepts
  rw [pair_interface,PolicySourceInterfaceProof.code hΓ a av ac ha hac,
    PolicySourceInterfaceProof.code hΓ b bv bc hb hbc]
  simp only [bind,pure,Option.bind_some,Option.any_some,Bool.and_eq_true_iff,CompiledVector.syntaxCode,
    check_exact,finite_compiled av ac ha hac,finite_compiled bv bc hb hbc]

theorem raw_class (p : Policy) (q : SourceCode.Input) :
    PolicyFinite.accepts p q=true ↔
    ∃ (τ υ : Ty) (a : OriginalTerm (List.replicate q.1 Ty.ground) τ)
      (b : OriginalTerm (List.replicate q.1 Ty.ground) υ),
      SyntaxCode.encodeTerm a=q.2.2.1 ∧ SyntaxCode.encodeTerm b=q.2.2.2 ∧
      PolicyFinite.FiniteSource p a ∧ PolicyFinite.FiniteSource p b := by
  let Γ := List.replicate q.1 Ty.ground
  have hg : ∀ σ ∈ Γ,σ=Ty.ground := by simp [Γ]
  constructor
  · intro h
    obtain ⟨aa,ha,bb,hb,hcheck⟩ : ∃ aa,PolicySourceInterface.compile p q.1 q.2.2.1=some aa ∧
        ∃ bb,PolicySourceInterface.compile p q.1 q.2.2.2=some bb ∧
          PolicyFinite.finiteScalarCode aa.1=true ∧ PolicyFinite.finiteScalarCode bb.1=true := by
      unfold PolicyFinite.accepts at h
      rw [pair_interface] at h
      cases ha : PolicySourceInterface.compile p q.1 q.2.2.1 with
      | none => simp [ha] at h
      | some aa =>
        cases hb : PolicySourceInterface.compile p q.1 q.2.2.2 with
        | none => simp [ha,hb] at h
        | some bb => exact ⟨aa,rfl,bb,rfl,by simpa [ha,hb] using h⟩
    obtain ⟨τ,a,av,ac,ea,hav,hac,hca⟩ := (PolicySourceInterfaceProof.raw p q.1 q.2.2.1 aa).mp ha
    obtain ⟨υ,b,bv,bc,eb,hbv,hbc,hcb⟩ := (PolicySourceInterfaceProof.raw p q.1 q.2.2.2 bb).mp hb
    refine ⟨τ,υ,a,b,ea,eb,(finite_compiled av ac hav hac).mpr ?_,(finite_compiled bv bc hbv hbc).mpr ?_⟩
    · apply (check_exact _ _ ac.scalar).mp
      simpa only [←hca,CompiledVector.syntaxCode] using hcheck.1
    · apply (check_exact _ _ bc.scalar).mp
      simpa only [←hcb,CompiledVector.syntaxCode] using hcheck.2
  · rintro ⟨τ,υ,a,b,ea,eb,ha,hb⟩
    have h := (typed_accepts p Γ hg τ υ a b q.2.1).mpr ⟨ha,hb⟩
    simpa only [Γ,List.length_replicate,ea,eb] using h
end LogicLineages.StandardControlCurrent.PolicyFiniteProof
