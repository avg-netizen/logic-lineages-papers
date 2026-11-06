module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaApplicationDecoderProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaApplicationProof
open Source NumberedLeastCodeRepresentative JointGammaApplication
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem calibration (n : Nat) (arity : Fin n → Nat) (context domain codomain f a z : Nat) :
    applicationValue n arity (List.Vector.ofFn ![context,domain,codomain,f,a,z]) = 1 ↔
      encodedApplication n arity context domain codomain f a z := by
  cases hf : Encodable.decode (α := ContextUniform.Object) f with
  | none => simp [applicationValue,encodedApplication,hf]
  | some fobj =>
    rcases fobj with ⟨Gamma,x⟩
    cases ha : Encodable.decode (α := ContextUniform.Object) a with
    | none => simp [applicationValue,encodedApplication,hf,ha]
    | some aobj =>
      rcases aobj with ⟨Delta,y⟩
      cases hz : Encodable.decode (α := ContextUniform.Object) z with
      | none => simp [applicationValue,encodedApplication,hf,ha,hz]
      | some zobj =>
        rcases zobj with ⟨Xi,value⟩
        by_cases hga : Gamma = Delta
        · subst Delta
          by_cases hgz : Gamma = Xi
          · subst Xi
            simpa [applicationValue,encodedApplication,hf,ha,hz] using
              OrdinaryArithmeticApplicationSupportProof.valueCalibration n arity Gamma context domain codomain x y value
          · simp [applicationValue,encodedApplication,hf,ha,hz,hgz,Ne.symm hgz]
        · simp [applicationValue,encodedApplication,hf,ha,hz,hga,Ne.symm hga]

theorem actualOriginalContextFibers : JointGammaApplicationTargets.ActualOriginalContextFibers := by
  intro n arity Gamma context domain codomain x y z
  simp [encodedApplication,ContextUniform.objectCode]

theorem actualNoCrossContextApplications : JointGammaApplicationTargets.ActualNoCrossContextApplications := by
  intro n arity Gamma Delta Xi context domain codomain x y z hne
  rintro ⟨Theta,a,b,c,hf,ha,hz,_⟩
  simp only [ContextUniform.objectCode,Encodable.encodek,Option.some.injEq,Prod.mk.injEq] at hf ha hz
  rcases hne with hne | hne
  · exact hne (hf.1.trans ha.1.symm)
  · exact hne (hf.1.trans hz.1.symm)

theorem actualApplicationArithmeticFormula : JointGammaApplicationTargets.ActualApplicationArithmeticFormula := by
  intro n arity
  obtain ⟨p,hp⟩ := Proof.allPrimitiveFunctions 6 (applicationValue n arity)
    (JointGammaApplicationDecoderProof.actualObjectApplicationPrimitive n arity)
  have hphi : ∀ context domain codomain f a z : Nat,
      (applicationFormula p).Realize ![context,domain,codomain,f,a,z] ↔
        encodedApplication n arity context domain codomain f a z := by
    intro context domain codomain f a z
    rw [applicationFormula,OrdinaryArithmeticProgramProof.appliedProgramGraphTruth,hp]
    exact calibration n arity context domain codomain f a z
  refine ⟨p,hp,hphi,?_⟩
  intro symbols S hc table Gamma sigma tau f a hf ha z
  rw [hphi,actualOriginalContextFibers,OrdinaryArithmeticApplicationSupportProof.concreteCalibration,
    NumberedNumericApplicationProof.canonicalApplicationCalibration n arity symbols S hc Gamma sigma tau f a hf ha]
  simp only [Option.some.injEq]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaApplicationProof
