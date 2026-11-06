module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaTypedPrimitiveProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaTypedProof
open Source NumberedLeastCodeRepresentative JointGammaTyped
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem calibration (n : Nat) (arity : Fin n → Nat) (context typ object : Nat) :
    typedValue n arity (List.Vector.ofFn ![context,typ,object]) = 1 ↔
      encodedTyped n arity context typ object := by
  cases hd : Encodable.decode (α := ContextUniform.Object) object with
  | none => simp [typedValue,encodedTyped,hd]
  | some obj =>
    rcases obj with ⟨Gamma,value⟩
    simpa [typedValue,encodedTyped,hd] using
      OrdinaryArithmeticTypedCarrierSupportProof.calibration n arity Gamma context typ value

theorem actualOriginalContextFibers : JointGammaTypedTargets.ActualOriginalContextFibers := by
  intro n arity Gamma context typ value
  simp [encodedTyped,ContextUniform.objectCode]

theorem actualTypedArithmeticFormula : JointGammaTypedTargets.ActualTypedArithmeticFormula := by
  intro n arity
  obtain ⟨p,hp⟩ := Proof.allPrimitiveFunctions 3 (typedValue n arity)
    (JointGammaTypedPrimitiveProof.actualObjectTypedPrimitive n arity)
  have hphi : ∀ context typ object : Nat,
      (typedFormula p).Realize ![context,typ,object] ↔ encodedTyped n arity context typ object := by
    intro context typ object
    rw [typedFormula,OrdinaryArithmeticProgramProof.appliedProgramGraphTruth,hp]
    exact calibration n arity context typ object
  refine ⟨p,hp,hphi,?_⟩
  intro symbols S hc table Gamma tau value
  rw [hphi,actualOriginalContextFibers]
  have ht := NumberedNumericDecodingProof.typeNumericRoundTrip tau
  simpa [OrdinaryArithmeticTypedCarrier.encodedTyped,OrdinaryArithmeticQuotient.contextCode,ht] using
    NumberedTypedCarrierProof.typedCanonicalCarrier n arity symbols S hc Gamma tau value

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaTypedProof
