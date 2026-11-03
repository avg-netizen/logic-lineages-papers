module
public import LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryBetaDiagnosticConsequencesTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryBetaDiagnosticConsequencesProof
open Source Source.SourceMarkedSyntax Source.SourceTypeSupport RecursiveComparison
open OrdinaryBetaTransitivityDiagnostic OrdinaryBetaTransitivityDiagnosticProof

theorem strictFirst : Strict Nat arity above [] ⟨.ground,embed pOriginal⟩ ⟨.ground,embed tOriginal⟩ := by
  have hpt := OrdinaryBetaTransitivityDiagnosticStepsProof.ordinarySteps.1
  obtain ⟨n,hn⟩ := OriginalDerivationBudgetCompletenessProof.weakComplete above hpt
  have H : ∀ n,OriginalDerivationBudget.Weak Nat arity above n [] ⟨.ground,p⟩ ⟨.ground,t⟩ →
      Weak Nat arity above [] ⟨.ground,q⟩ ⟨.ground,t⟩ := by
    intro n
    induction n with
    | zero => intro hw; cases hw
    | succ n ih =>
      intro hw
      rcases OriginalBudgetFunctionalInversionProof.ordinaryFrame above n _ _ hw
        (.application .ground .ground) (.ranked 3) applicationBase (.cons k (.cons z .nil)) rfl rfl
        with ⟨he,matched,hperm,hm⟩ | hmark | hup
      · cases he
      · exact OriginalDerivationBudgetErasureProof.weakSound hmark
      · exact ih hup
  exact .mark p q t rfl (H n hn)

theorem confinedWitness : OrdinaryBetaDiagnosticConsequencesTargets.ActualConfinedWitness := by
  have steps := OrdinaryBetaTransitivityDiagnosticStepsProof.ordinarySteps
  have htp : typeSupport tOriginal ⊆ typeSupport pOriginal := by decide
  have hut : typeSupport uOriginal ⊆ typeSupport tOriginal := by decide
  exact ⟨⟨steps.1,htp⟩,⟨steps.2,hut⟩,fun hpu => ordinaryFailure hpu.1⟩

theorem strictChain : OrdinaryBetaDiagnosticConsequencesTargets.ActualStrictChain := by
  exact ⟨strictFirst,OrdinaryBetaTransitivityDiagnosticStepsProof.ordinarySteps.2,
    fun hpu => ordinaryFailure (RecursiveComparisonProof.strictWeakInclusion Nat arity above [] _ _ hpu)⟩

theorem strictWeakRefutation : OrdinaryBetaDiagnosticConsequencesTargets.ActualStrictWeakRefutation := by
  intro H
  have habove : Transitive above := fun _ _ _ hab hbc => Nat.lt_trans hbc hab
  have htu := RecursiveComparisonProof.strictWeakInclusion Nat arity above [] _ _
    OrdinaryBetaTransitivityDiagnosticStepsProof.ordinarySteps.2
  exact ordinaryFailure (RecursiveComparisonProof.strictWeakInclusion Nat arity above [] _ _
    (H Nat arity above habove [] .ground pOriginal tOriginal uOriginal strictFirst htu))

theorem rawEndpointRefutation : OrdinaryBetaDiagnosticConsequencesTargets.ActualRawEndpointRefutation := by
  intro H
  have habove : Transitive above := fun _ _ _ hab hbc => Nat.lt_trans hbc hab
  have steps := OrdinaryBetaTransitivityDiagnosticStepsProof.ordinarySteps
  have htu := RecursiveComparisonProof.strictWeakInclusion Nat arity above [] _ _ steps.2
  exact ordinaryFailure (H Nat arity above habove [] ⟨.ground,p⟩ ⟨.ground,t⟩ ⟨.ground,u⟩
    steps.1 htu (SourceUnmarkedProof.ordinaryEmbedding Nat arity [] .ground uOriginal))

end LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryBetaDiagnosticConsequencesProof
