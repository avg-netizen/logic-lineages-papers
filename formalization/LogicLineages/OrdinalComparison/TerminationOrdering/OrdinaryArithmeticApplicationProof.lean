module
public import LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticApplicationSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticApplicationProof
open Source OrdinaryArithmetic OrdinaryArithmeticQuotient OrdinaryArithmeticApplication
open OrdinaryArithmeticApplicationSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem applicationValuePrimitive : OrdinaryArithmeticApplicationTargets.ActualApplicationValuePrimitive := valuePrimitive

theorem partialApplicationFormula : OrdinaryArithmeticApplicationTargets.ActualPartialApplicationFormula := by
  intro n arity Gamma
  obtain ⟨p,hp⟩ := Proof.allPrimitiveFunctions 6 (applicationValue n arity Gamma) (valuePrimitive n arity Gamma)
  let phi : Formula (Fin 6) := applyGraph (graphFormula p) (succTerm zeroTerm) ![.var 0,.var 1,.var 2,.var 3,.var 4,.var 5]
  have hphi : ∀ context domain codomain x y z : Nat,
      phi.Realize ![context,domain,codomain,x,y,z] ↔ decodedApplication n arity Gamma context domain codomain x y = some z := by
    intro context domain codomain x y z
    change (applyGraph (graphFormula p) (succTerm zeroTerm) ![.var 0,.var 1,.var 2,.var 3,.var 4,.var 5]).Realize _ ↔ _
    rw [OrdinaryArithmeticProgramProof.appliedProgramGraphTruth,hp]
    exact valueCalibration n arity Gamma context domain codomain x y z
  refine ⟨phi,hphi,?_⟩
  intro symbols S table sigma tau x y z
  rw [hphi,concreteCalibration]

theorem applicationFormulaCalibration : OrdinaryArithmeticApplicationTargets.ActualApplicationFormulaCalibration := by
  intro n arity Gamma
  obtain ⟨phi,hphi,hconcrete⟩ := partialApplicationFormula n arity Gamma
  refine ⟨phi,hphi,?_⟩
  intro symbols S hc table sigma tau f a hf ha z
  rw [hconcrete]
  have h := NumberedNumericApplicationProof.canonicalApplicationCalibration n arity symbols S hc Gamma sigma tau f a hf ha
  rw [h]
  simp only [Option.some.injEq]

end LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticApplicationProof
