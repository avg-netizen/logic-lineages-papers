module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaDomainCodecProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaTypedProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaDomainProof
open Source JointGammaDomain JointGammaDomainCodecProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

attribute [local irreducible] Primrec

theorem actualGuardPrimitive : JointGammaDomainTargets.ActualGuardPrimitive := by
  have getP (i : Fin 2) : Primrec (fun v : List.Vector Nat 2 => v.get i) :=
    Primrec.vector_get.comp Primrec.id (Primrec.const i)
  have hf := JointGammaProgramsDecoderProof.objectDecoderPrimitive.comp (getP 0)
  have ha : Primrec (fun p : List.Vector Nat 2 × ContextUniform.Object =>
      Encodable.decode (α := ContextUniform.Object) (p.1.get 1)) :=
    JointGammaProgramsDecoderProof.objectDecoderPrimitive.comp ((getP 1).comp Primrec.fst)
  have hb : Primrec (fun p : (List.Vector Nat 2 × ContextUniform.Object) × ContextUniform.Object =>
      decide (p.1.2.1 = p.2.1)) :=
    (Primrec.eq.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
      (Primrec.fst.comp Primrec.snd)).decide
  have hi := NumberedQuotientPathPrimrecSupportProof.optionAnyPrimitive ha hb.to₂
  apply ((Primrec.dom_bool Bool.toNat).comp
    (NumberedQuotientPathPrimrecSupportProof.optionAnyPrimitive hf hi.to₂)).of_eq
  intro v
  cases hd : Encodable.decode (α := ContextUniform.Object) (v.get 0) <;>
    cases he : Encodable.decode (α := ContextUniform.Object) (v.get 1) <;>
    simp only [guardValue,hd,he,Option.any_none,Option.any_some,Bool.toNat_false]

theorem actualGuardCalibration : JointGammaDomainTargets.ActualGuardCalibration := by
  constructor
  · intro f a
    cases hf : Encodable.decode (α := ContextUniform.Object) f with
    | none => simp [guardValue,sameContext,hf]
    | some fobj =>
      rcases fobj with ⟨Gamma,x⟩
      cases ha : Encodable.decode (α := ContextUniform.Object) a with
      | none => simp [guardValue,sameContext,hf,ha]
      | some aobj =>
        rcases aobj with ⟨Delta,y⟩
        simp [guardValue,sameContext,hf,ha,OrdinaryArithmeticQuotientProof.boolNatOne,eq_comm]
  · intro Gamma Delta x y
    simp [sameContext,ContextUniform.objectCode,eq_comm]

theorem actualArgumentDomain : JointGammaDomainTargets.ActualArgumentDomain := by
  intro Gamma x u
  constructor
  · rintro ⟨Delta,a,b,hf,hu⟩
    simp only [ContextUniform.objectCode,Encodable.encodek,Option.some.injEq,Prod.mk.injEq] at hf
    rcases hf with ⟨he,_⟩
    subst Delta
    exact ⟨b,((actualObjectCodec.2.1 u (Gamma,b)).mp hu).symm⟩
  · rintro ⟨a,rfl⟩
    exact ⟨Gamma,x,a,Encodable.encodek _,Encodable.encodek _⟩

theorem actualQuantifierFibers : JointGammaDomainTargets.ActualQuantifierFibers := by
  intro Gamma x Q
  constructor
  · constructor
    · intro h a
      exact h _ ((actualArgumentDomain Gamma x _).mpr ⟨a,rfl⟩)
    · intro h u hu
      obtain ⟨a,rfl⟩ := (actualArgumentDomain Gamma x u).mp hu
      exact h a
  · constructor
    · rintro ⟨u,hu,hq⟩
      obtain ⟨a,rfl⟩ := (actualArgumentDomain Gamma x u).mp hu
      exact ⟨a,hq⟩
    · rintro ⟨a,hq⟩
      exact ⟨ContextUniform.objectCode Gamma a,(actualArgumentDomain Gamma x _).mpr ⟨a,rfl⟩,hq⟩

theorem actualTypedArgumentFibers : JointGammaDomainTargets.ActualTypedArgumentFibers := by
  intro n arity Gamma context typ x Q
  rw [(actualQuantifierFibers Gamma x
    (fun u => JointGammaTyped.encodedTyped n arity context typ u → Q u)).1]
  apply forall_congr'
  intro a
  exact imp_congr (JointGammaTypedProof.actualOriginalContextFibers n arity Gamma context typ a) Iff.rfl

theorem actualGuardArithmeticFormula : JointGammaDomainTargets.ActualGuardArithmeticFormula := by
  obtain ⟨p,hp⟩ := Proof.allPrimitiveFunctions 2 guardValue actualGuardPrimitive
  refine ⟨p,hp,?_⟩
  intro f a
  rw [SourcePresentation.checkerFormula,OrdinaryArithmeticProgramProof.appliedProgramGraphTruth,hp]
  exact actualGuardCalibration.1 f a

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaDomainProof
