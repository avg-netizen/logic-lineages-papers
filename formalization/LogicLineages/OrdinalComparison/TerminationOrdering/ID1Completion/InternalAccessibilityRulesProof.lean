module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAccessibilityRulesSyntaxProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAccessibilityRulesProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalAccessibilityRules
open InternalAccessibilityRulesSyntaxProof InternalSourceIntroductionProof
open InternalPositiveUnfoldingSupportProof InternalRecursionClosureLogicProof
open InternalTagArithmeticSyntaxProof (emb)

theorem actualOriginalMembershipEquation :
    InternalAccessibilityRulesTargets.ActualOriginalMembershipEquation := by
  intro data odd context α x
  cases odd with
  | false =>
    have h := actualInternalScalarEquation data context α x
    change Nonempty (Derivation _ [] ((membership false x).iff
      (SourceEndpoint.substitutePositive ![SourceComputabilityFormulaSupportProof.numeral context,x]
        (PositiveArithmeticTransforms.tagPredicate false
          (accessibilityOperator (SourcePresentation.checkerFormula data.scalar)
            (OrdinaryArithmeticQuotient.certificateGraph data.positive)))).formula)) at h
    have hn := originalPayload data false context x
    dsimp only [carrierProgram,edgeProgram] at hn
    rw [hn] at h
    exact h
  | true =>
    have h := actualInternalMultisetEquation data context α x
    change Nonempty (Derivation _ [] ((membership true x).iff
      (SourceEndpoint.substitutePositive ![SourceComputabilityFormulaSupportProof.numeral context,x]
        (PositiveArithmeticTransforms.tagPredicate true
          (accessibilityOperator (SourcePresentation.checkerFormula data.multiset)
            (OrdinaryArithmeticQuotient.certificateGraph data.direct)))).formula)) at h
    have hn := originalPayload data true context x
    dsimp only [carrierProgram,edgeProgram] at hn
    rw [hn] at h
    exact h

theorem unfolding {data : SourcePresentation.Data} {odd : Bool} {context : Nat} {α : Type}
    {Gamma : List (Formula α)} {x : OrdinaryArithmetic.Term α}
    (h : Nonempty (Derivation (SourcePresentation.sourceBody data context) Gamma (membership odd x))) :
    Nonempty (Derivation (SourcePresentation.sourceBody data context) Gamma
      (carrier data odd context x ⊓ successors data odd context x)) := by
  obtain ⟨eq⟩ := actualOriginalMembershipEquation data odd context α x
  exact closedApply ⟨Derivation.conjunctionLeft eq⟩ h

theorem actualOriginalCarrierExtraction :
    InternalAccessibilityRulesTargets.ActualOriginalCarrierExtraction := by
  intro data odd context α Gamma x h
  obtain ⟨d⟩ := unfolding h
  exact ⟨Derivation.conjunctionLeft d⟩

theorem actualOriginalSuccessorClosure :
    InternalAccessibilityRulesTargets.ActualOriginalSuccessorClosure := by
  intro data odd context α Gamma x y hi ⟨he⟩
  obtain ⟨d⟩ := unfolding hi
  have hs := Derivation.universalElimination (emb y) (Derivation.conjunctionRight d)
  rw [InternalAccessibilityRulesSyntaxProof.successorInstance] at hs
  exact ⟨Derivation.implicationElimination hs he⟩

/-- Introduce precisely the existing existential certificate, using its
original witness term. No decidability or semantic reflection is involved. -/
theorem edgeIntroduction {body : Positive (Fin 1)} {data : SourcePresentation.Data} {odd : Bool}
    {context : Nat} {α : Type} {Gamma : List (Formula α)}
    {x y witness : OrdinaryArithmetic.Term α}
    (h : Nonempty (Derivation body Gamma (certificate data odd context x y witness))) :
    Nonempty (Derivation body Gamma (edge data odd context x y)) := by
  obtain ⟨h⟩ := h
  rw [edgeExists]
  apply Nonempty.intro
  apply Derivation.existentialIntroduction (emb witness)
  rw [certificateInstance]
  exact h

theorem actualOriginalCertifiedSuccessorClosure :
    InternalAccessibilityRulesTargets.ActualOriginalCertifiedSuccessorClosure := by
  intro data odd context α Gamma x y witness hi hc
  exact actualOriginalSuccessorClosure data odd context α Gamma x y hi (edgeIntroduction hc)

theorem actualOriginalAccessibilityIntroduction :
    InternalAccessibilityRulesTargets.ActualOriginalAccessibilityIntroduction := by
  intro data odd context α Gamma x ⟨hc⟩ ⟨hs⟩
  obtain ⟨eq⟩ := actualOriginalMembershipEquation data odd context α x
  exact closedApply ⟨Derivation.conjunctionRight eq⟩
    ⟨Derivation.conjunctionIntroduction hc hs⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAccessibilityRulesProof
