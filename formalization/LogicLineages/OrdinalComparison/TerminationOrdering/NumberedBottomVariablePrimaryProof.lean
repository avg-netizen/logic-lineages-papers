module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedBottomVariableExchangeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPrimaryExchangeProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedBottomVariablePrimaryProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedPrimarySubstitution
open NumberedBottomVariable NumberedPrimaryExchange NumberedWindowEquivalence

theorem actualPrimaryInverse : NumberedBottomVariableLiftingTargets.ActualPrimaryInverse := by
  intro Symbol arity symbols S Gamma Delta theta ht q r hp
  have hlift : ∀ (source : Packed Symbol arity Gamma) (target : Packed Symbol arity Delta),
      Exchange Symbol arity symbols S Delta (substitutePacked theta source) target →
      ∃ source', substitutePacked theta source' = target ∧
        Exchange Symbol arity symbols S Gamma source source' := by
    intro source target he
    obtain ⟨source',hs,himage⟩ := NumberedBottomVariableExchangeProof.actualExchangeInverse
      Symbol arity symbols S Gamma Delta theta ht source target he
    exact ⟨source',himage,hs⟩
  obtain ⟨q',he,hchain⟩ := NumberedPrimaryExchangeSupportProof.chainLift (substitutePacked theta)
    hlift (NumberedPrimaryExchangeProof.primaryToClosure hp) q rfl
  exact ⟨q',NumberedPrimaryExchangeProof.closureToPrimary hchain,he⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedBottomVariablePrimaryProof
