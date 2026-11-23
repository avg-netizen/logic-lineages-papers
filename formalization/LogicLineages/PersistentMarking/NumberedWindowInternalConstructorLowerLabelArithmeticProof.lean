module
public import LogicLineages.PersistentMarking.NumberedWindowInternalConstructorLowerLabelTargets
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalOrderProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestCompositionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportEvaluationSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalConstructorLowerLabelArithmeticProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open ID1Completion.InternalSourceInversionSupportProof (onEquality)
open ID1Completion.InternalOriginalOrderProof (actualOriginalOrderIntroduction)
open ID1Completion.InternalControlGraphSupportProof (projectionValue successorValue valueUnique equalEqn)
open ID1Completion.InternalApplicationCertificateConstructorsSupportProof (unaryValue)
open ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof (formulaCases withHyp)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open ID1Completion.InternalTagArithmeticSupportProof (trans symm addSucc addZero congSuc sucNeZeroApply)
open ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransport (sameOf succOf)
open ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorSupportProof (sameReject)
open ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportEvaluationSupportProof (sameOfEvaluation)
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalConstructorLowerLabelTargets

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem openLowerEquality (src dst : OTerm α)
    (h : Nonempty (Derivation B Γ (programGraph lowerLabel (suc z) ![src,dst]))) :
    Nonempty (Derivation B Γ (eqn src (suc dst))) := by
  let E := eqn src (suc dst)
  let xs : Fin 2 → OTerm α := ![src,dst]
  apply formulaCases E
  · exact ⟨Derivation.hypothesis List.mem_cons_self⟩
  · have bad : Nonempty (Derivation B (E.not :: Γ) (equal src (suc dst)).not) := by
      rw [equalEqn]
      exact ⟨Derivation.hypothesis List.mem_cons_self⟩
    have sr : Nonempty (Derivation B (E.not :: Γ)
        (programGraph (succOf (.projection 1)) (suc dst) xs)) :=
      unaryValue .succ (.projection 1) (suc dst) dst xs
        (successorValue (Fin.cons dst Fin.elim0)) (projectionValue 1 xs)
    have r0 : Nonempty (Derivation B (E.not :: Γ) (programGraph lowerLabel z xs)) :=
      sameReject (.projection 0) (succOf (.projection 1)) src (suc dst) xs
        (projectionValue 0 xs) sr bad
    obtain ⟨contr⟩ := valueUnique lowerLabel (suc z) z xs (withHyp h E.not) r0
    exact ⟨Derivation.explosion (sucNeZeroApply contr)⟩

theorem exactOpenLowerLabel : ExactOpenLowerLabel := by
  intro B α Γ src dst h
  obtain ⟨same⟩ := openLowerEquality src dst h
  have addOne : Derivation B Γ (eqn (OrdinaryArithmetic.addTerm dst (suc z)) (suc dst)) :=
    trans (addSucc dst z) (congSuc (addZero dst))
  have connected : Derivation B Γ (eqn (OrdinaryArithmetic.addTerm dst (suc z)) src) :=
    ID1Completion.InternalTagArithmeticSupportProof.trans addOne
      (ID1Completion.InternalTagArithmeticSupportProof.symm same)
  have embedded : Nonempty (Derivation B Γ (arithmeticEmbedding.onFormula
      ((OrdinaryArithmetic.addTerm dst (OrdinaryArithmetic.succTerm z)).equal src))) := by
    rw [onEquality]
    exact ⟨connected⟩
  have strict : Nonempty (Derivation B Γ (ltF dst src)) :=
    actualOriginalOrderIntroduction B α Γ dst src z embedded
  obtain ⟨lt⟩ := strict
  exact ⟨Derivation.conjunctionIntroduction same lt⟩

theorem exactNumericLowerLabel : ExactNumericLowerLabel := by
  intro src dst
  rw [lowerLabel,sameOfEvaluation]
  change (if src = dst + 1 then 1 else 0) = _
  cases src with
  | zero => simp
  | succ pred =>
    by_cases h : pred = dst <;> simp [h]

end LogicLineages.PersistentMarking.NumberedWindowInternalConstructorLowerLabelArithmeticProof
