module

public import LogicLineages.NativeModule.PersistentMarking.ConditionalUpperUniformTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAccessibilityRulesSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalNumeralEvaluationStatementChecks

/-! Step (ii) of the uniform bridge: the scalar carrier formula at numerals c, x is derivable
whenever the scalar checker evaluates to 1 there.  The derivation is the accepted numeral
evaluation of the checker program (`numeral_evaluation_exact`); the only work is the syntactic
identification of `carrier d false c (numeral x)` with that graph instance. -/

@[expose] public section

namespace LogicLineages.PersistentMarking.ConditionalUpperUniformCarrierProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators PositiveArithmeticTransforms SourceComputabilityFormulaSupportProof
open ID1Completion.InternalCalculus ID1Completion.InternalAccessibilityRules ID1Completion.SourcePresentation
open ID1Completion.InternalAccessibilityRulesSyntaxProof ID1Completion.InternalTermSubstitutionSyntaxProof
open ID1Completion.InternalGraphComposition
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open ConditionalUpperUniformTargets

theorem carrierAsGraph (d : Data) (c x : Nat) :
    carrier (α := Empty) d false c (numeral x) =
      graph (OrdinaryArithmetic.graphFormula d.scalar) (numeral 1)
        (fun i => (numeral ((c ::ᵥ x ::ᵥ List.Vector.nil).get i) : OTerm Empty)) := by
  unfold carrier graph
  congr 1
  change ((OrdinaryArithmetic.graphFormula d.scalar).subst
      (Fin.cases (OrdinaryArithmetic.succTerm OrdinaryArithmetic.zeroTerm) ![.var 0, .var 1])).subst
        ![numeral c, numeral x] =
    (OrdinaryArithmetic.graphFormula d.scalar).subst
      (Fin.cases (numeral 1) (fun i => numeral ((c ::ᵥ x ::ᵥ List.Vector.nil).get i)))
  rw [formulaSubstComposition]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact numeralSubst 1 _
  · refine Fin.cases ?_ (fun k => ?_) j
    · rfl
    · refine Fin.cases ?_ (fun l => Fin.elim0 l) k
      rfl

theorem exact_ScalarCarrierNumeralTruth : ScalarCarrierNumeralTruth := by
  intro B d c x one
  obtain ⟨h⟩ := ID1Completion.InternalNumeralEvaluationStatementChecks.numeral_evaluation_exact B 2 d.scalar
    (c ::ᵥ x ::ᵥ List.Vector.nil) Empty
  rw [one] at h
  rw [carrierAsGraph]
  exact ⟨h⟩

#print axioms exact_ScalarCarrierNumeralTruth

end LogicLineages.PersistentMarking.ConditionalUpperUniformCarrierProof
