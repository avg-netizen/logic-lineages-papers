module
public import LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticTypedCarrierSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticTypedCarrierProof
open Source OrdinaryArithmetic OrdinaryArithmeticQuotient OrdinaryArithmeticTypedCarrier
open OrdinaryArithmeticTypedCarrierSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem typedCheckerPrimitive : OrdinaryArithmeticTypedCarrierTargets.ActualTypedCheckerPrimitive := checkerPrimitive

theorem encodedTypedPrimitive : OrdinaryArithmeticTypedCarrierTargets.ActualEncodedTypedPrimitive := wrapperPrimitive

theorem typedArithmeticFormula : OrdinaryArithmeticTypedCarrierTargets.ActualTypedArithmeticFormula := by
  intro n arity Gamma
  obtain ⟨p,hp⟩ := Proof.allPrimitiveFunctions 3 (typedValue n arity Gamma) (wrapperPrimitive n arity Gamma)
  let phi : Formula (Fin 3) := applyGraph (graphFormula p) (succTerm zeroTerm) ![.var 0,.var 1,.var 2]
  have hphi : ∀ context typ value : Nat, phi.Realize ![context,typ,value] ↔ encodedTyped n arity Gamma context typ value := by
    intro context typ value
    change (applyGraph (graphFormula p) (succTerm zeroTerm) ![.var 0,.var 1,.var 2]).Realize ![context,typ,value] ↔ _
    rw [OrdinaryArithmeticProgramProof.appliedProgramGraphTruth,hp]
    exact calibration n arity Gamma context typ value
  refine ⟨phi,hphi,?_⟩
  intro symbols S hc table tau value
  refine (hphi (contextCode symbols S table) (NumberedLeastCodeRepresentative.typeNumber tau) value).trans ?_
  have ht : NumberedNumericDecoding.decodeType (NumberedLeastCodeRepresentative.typeNumber tau) = some tau :=
    NumberedNumericDecodingProof.typeNumericRoundTrip tau
  simpa [encodedTyped,contextCode,ht] using
    NumberedTypedCarrierProof.typedCanonicalCarrier n arity symbols S hc Gamma tau value

end LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticTypedCarrierProof
