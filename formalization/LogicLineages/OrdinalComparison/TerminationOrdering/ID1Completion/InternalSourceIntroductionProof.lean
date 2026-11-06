module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceIntroductionSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceInversionProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceIntroductionProof
open FirstOrder Language PositiveArithmeticOperators PositiveArithmeticTransforms
open InternalCalculus SourceEndpoint TaggedArithmeticOperators SourceComputabilityFormulaSupportProof
open InternalPositiveUnfoldingSupportProof InternalTermSubstitutionProof InternalSourceInversionProof
open InternalSourceIntroductionSupportProof

theorem actualInternalScalarEquation : InternalSourceIntroductionTargets.ActualInternalScalarEquation := by
  intro data context α t
  obtain ⟨forward⟩ := actualInternalScalarInversion data context α t
  obtain ⟨unfolding⟩ := actualExplicitSourceUnfolding data context α (tagTerm false t)
  obtain ⟨branch⟩ := actualTaggedBranchIntroduction (SourcePresentation.sourceBody data context) α false
    (SourcePresentation.scalarOperator data) (numeral context) t
  obtain ⟨opposite⟩ := actualOppositeBranch (SourcePresentation.sourceBody data context) α false
    (SourcePresentation.multisetOperator data) (numeral context) t
  apply Nonempty.intro
  apply Derivation.conjunctionIntroduction forward
  apply Derivation.implicationIntroduction
  let Gamma : List (Formula α) :=
    [(substitutePositive ![numeral context,t] (tagPredicate false (SourcePresentation.scalarOperator data))).formula]
  have hbranch := Derivation.implicationElimination (weakenClosed branch Gamma)
    (Derivation.hypothesis List.mem_cons_self)
  have hbody := Derivation.conjunctionIntroduction hbranch (weakenClosed opposite Gamma)
  exact Derivation.implicationElimination (weakenClosed (Derivation.conjunctionRight unfolding) Gamma) hbody

theorem actualInternalMultisetEquation : InternalSourceIntroductionTargets.ActualInternalMultisetEquation := by
  intro data context α t
  obtain ⟨forward⟩ := actualInternalMultisetInversion data context α t
  obtain ⟨unfolding⟩ := actualExplicitSourceUnfolding data context α (tagTerm true t)
  obtain ⟨branch⟩ := actualTaggedBranchIntroduction (SourcePresentation.sourceBody data context) α true
    (SourcePresentation.multisetOperator data) (numeral context) t
  obtain ⟨opposite⟩ := actualOppositeBranch (SourcePresentation.sourceBody data context) α true
    (SourcePresentation.scalarOperator data) (numeral context) t
  apply Nonempty.intro
  apply Derivation.conjunctionIntroduction forward
  apply Derivation.implicationIntroduction
  let Gamma : List (Formula α) :=
    [(substitutePositive ![numeral context,t] (tagPredicate true (SourcePresentation.multisetOperator data))).formula]
  have hbranch := Derivation.implicationElimination (weakenClosed branch Gamma)
    (Derivation.hypothesis List.mem_cons_self)
  have hbody := Derivation.conjunctionIntroduction (weakenClosed opposite Gamma) hbranch
  exact Derivation.implicationElimination (weakenClosed (Derivation.conjunctionRight unfolding) Gamma) hbody

theorem actualUniformEquationsExist : InternalSourceIntroductionTargets.ActualUniformEquationsExist := by
  intro n arity
  obtain ⟨data,hcal⟩ := JointGammaProgramsProof.actualContextUniformPresentationExists n arity
  exact ⟨data,hcal,fun context α t => ⟨actualInternalScalarEquation data context α t,
    actualInternalMultisetEquation data context α t⟩⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceIntroductionProof
