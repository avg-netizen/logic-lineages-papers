module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ApplicationResultBuilderPrimitiveProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaDomainCodecProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ApplicationResultBuilderProof
open Source ApplicationResultBuilder
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem mapOriginalObject (Gamma : List Ty) (o : Option Nat) (z : Nat) :
    o.map (ContextUniform.objectCode Gamma) = some z ↔
    ∃ value, Encodable.decode (α := ContextUniform.Object) z = some (Gamma,value) ∧ o = some value := by
  cases o with
  | none => simp
  | some value =>
    simp only [Option.map_some,Option.some.injEq]
    constructor
    · intro h
      exact ⟨value,(JointGammaDomainCodecProof.actualObjectCodec.2.1 z (Gamma,value)).mpr h,rfl⟩
    · rintro ⟨v,hd,hv⟩
      subst v
      exact (JointGammaDomainCodecProof.actualObjectCodec.2.1 z (Gamma,value)).mp hd

theorem actualPartialCalibration : ApplicationResultBuilderTargets.ActualPartialCalibration := by
  intro n arity context domain codomain f a z
  cases hf : Encodable.decode (α := ContextUniform.Object) f with
  | none => simp [resultOption,JointGammaApplication.encodedApplication,hf]
  | some fobj =>
    rcases fobj with ⟨Gamma,x⟩
    cases ha : Encodable.decode (α := ContextUniform.Object) a with
    | none => simp [resultOption,JointGammaApplication.encodedApplication,hf,ha]
    | some aobj =>
      rcases aobj with ⟨Delta,y⟩
      by_cases h : Gamma = Delta
      · subst Delta
        simpa [resultOption,JointGammaApplication.encodedApplication,hf,ha] using
          mapOriginalObject Gamma
            (OrdinaryArithmeticApplication.decodedApplication n arity Gamma context domain codomain x y) z
      · simp [resultOption,JointGammaApplication.encodedApplication,hf,ha,h,Ne.symm h]

theorem partialTotal (n : Nat) (arity : Fin n → Nat) (v : List.Vector Nat 5) (z : Nat) :
    resultOption n arity v = some z ↔ successValue n arity v = 1 ∧ z = resultValue n arity v := by
  cases h : resultOption n arity v <;> simp [successValue,resultValue,h,eq_comm]

theorem actualTotalCalibration : ApplicationResultBuilderTargets.ActualTotalCalibration := by
  intro n arity context domain codomain f a z
  rw [JointGammaApplicationProof.calibration,← actualPartialCalibration,partialTotal]

theorem actualSuccessAndDefault : ApplicationResultBuilderTargets.ActualSuccessAndDefault := by
  intro n arity v
  cases h : resultOption n arity v <;> simp [successValue,resultValue,h]

theorem boolNatRange (b : Bool) : b.toNat = 0 ∨ b.toNat = 1 := by
  cases b <;> simp

theorem actualOriginalRange : ApplicationResultBuilderTargets.ActualOriginalRange := by
  intro n arity v
  cases hf : Encodable.decode (α := ContextUniform.Object) (v.get 3) <;>
    cases ha : Encodable.decode (α := ContextUniform.Object) (v.get 4) <;>
      cases hz : Encodable.decode (α := ContextUniform.Object) (v.get 5)
  all_goals simp only [JointGammaApplication.applicationValue,hf,ha,hz]
  all_goals try exact Or.inl trivial
  split_ifs
  · exact boolNatRange _
  · exact Or.inl rfl

theorem actualOriginalValue : ApplicationResultBuilderTargets.ActualOriginalValue := by
  intro n arity context domain codomain f a z
  split_ifs with h
  · exact (actualTotalCalibration n arity context domain codomain f a z).mpr h
  · rcases actualOriginalRange n arity (List.Vector.ofFn ![context,domain,codomain,f,a,z]) with hz | hz
    · exact hz
    · exact False.elim (h ((actualTotalCalibration n arity context domain codomain f a z).mp hz))

theorem actualRawUniqueness : ApplicationResultBuilderTargets.ActualRawUniqueness := by
  intro n arity context domain codomain f a z w hz hw
  have hz' := (actualPartialCalibration n arity context domain codomain f a z).mpr hz
  have hw' := (actualPartialCalibration n arity context domain codomain f a w).mpr hw
  exact Option.some.inj (hz'.symm.trans hw')

theorem actualProgramWitnesses : ApplicationResultBuilderTargets.ActualProgramWitnesses := by
  intro n arity
  obtain ⟨result,hr⟩ := Proof.allPrimitiveFunctions 5 (resultValue n arity)
    (ApplicationResultBuilderPrimitiveProof.actualPrimitive n arity).2.1
  obtain ⟨success,hs⟩ := Proof.allPrimitiveFunctions 5 (successValue n arity)
    (ApplicationResultBuilderPrimitiveProof.actualPrimitive n arity).2.2
  refine ⟨result,success,hr,hs,?_⟩
  intro context domain codomain f a z
  rw [hr,hs]
  exact actualTotalCalibration n arity context domain codomain f a z

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ApplicationResultBuilderProof
