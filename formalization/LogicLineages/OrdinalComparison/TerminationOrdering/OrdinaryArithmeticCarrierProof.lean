module
public import LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticCarrierSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticCarrierProof
open Source OrdinaryArithmetic OrdinaryArithmeticQuotient OrdinaryArithmeticCarrier
open OrdinaryArithmeticCarrierSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem carrierCheckersPrimitive : OrdinaryArithmeticCarrierTargets.ActualCarrierCheckersPrimitive := by
  intro n arity Gamma
  exact ⟨decodedScalarPrimitive n arity Gamma,decodedListPrimitive n arity Gamma⟩

theorem checkerFormula (f : List.Vector Nat 2 → Nat) (hf : Primrec f) :
    ∃ phi : Formula (Fin 2), ∀ context value : Nat,
      phi.Realize ![context,value] ↔ f (List.Vector.ofFn ![context,value]) = 1 := by
  obtain ⟨p,hp⟩ := Proof.allPrimitiveFunctions 2 f hf
  refine ⟨applyGraph (graphFormula p) (succTerm zeroTerm) ![.var 0,.var 1],?_⟩
  intro context value
  rw [OrdinaryArithmeticProgramProof.appliedProgramGraphTruth,hp]
  rfl

theorem encodedCarrierFormulas : OrdinaryArithmeticCarrierTargets.EncodedCarrierFormulas := by
  intro n arity Gamma
  obtain ⟨scalar,hs⟩ := checkerFormula (scalarValue n arity Gamma) (decodedScalarPrimitive n arity Gamma)
  obtain ⟨list,hl⟩ := checkerFormula (listValue n arity Gamma) (decodedListPrimitive n arity Gamma)
  refine ⟨scalar,list,?_⟩
  intro context value
  exact ⟨(hs context value).trans (scalarCalibration n arity Gamma context value),
    (hl context value).trans (listCalibration n arity Gamma context value)⟩

theorem typedCarrierFormulas : OrdinaryArithmeticCarrierTargets.ActualTypedCarrierFormulas := by
  intro n arity Gamma
  obtain ⟨scalar,list,h⟩ := encodedCarrierFormulas n arity Gamma
  refine ⟨scalar,list,?_⟩
  intro symbols S hc table x values
  constructor
  · have hs := (h (contextCode symbols S table) x).1
    have hc' := NumberedNumericCarrierProof.canonicalCarrierTestCorrect n arity symbols S hc Gamma x
    exact hs.trans (by simpa [encodedScalar,contextCode] using hc')
  · have hl := (h (contextCode symbols S table) (Encodable.encode values)).2
    have hc' := QuotientDirectCarrierProof.listCarrier n arity symbols S hc Gamma values
    exact hl.trans (by simpa [encodedList,contextCode] using hc')

end LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticCarrierProof
