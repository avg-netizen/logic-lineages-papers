module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceGroundProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceCompletionProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus
open GuardedSource GuardedSourceGround GuardedSourceGroundProof
open SourceComputabilityFormulaSupportProof NumberedLeastCodeRepresentative
open InternalPositiveUnfoldingSupportProof

/-- The same particular source and computability Programs give both the full
symbolic typed successor theorem and exact ground C downward closure. -/
theorem actualUniformGroundClosureExists : GuardedSourceTargets.ActualUniformGroundClosureExists := by
  intro n arity
  obtain ⟨source,comp,hs,hc,hder⟩ := GuardedSourceProof.actualUniformTypedSuccessorExists n arity
  refine ⟨source,comp,hs,hc,?_⟩
  intro symbols S table hclosed α
  refine ⟨hder symbols S table hclosed α,?_⟩
  intro x y
  let context := OrdinaryArithmeticQuotient.contextCode symbols S table
  change Nonempty (Derivation (SourcePresentation.sourceBody source context) []
    ((literalComputable comp context .ground x ⊓ literalR source context x y).imp
      (literalComputable comp context .ground y)))
  rw [groundFormula comp context α x,groundFormula comp context α y]
  obtain ⟨dt⟩ := hder symbols S table hclosed α (numeral (typeNumber .ground)) x y
  obtain ⟨ds⟩ := scalarDownward source context α x y
  apply Nonempty.intro
  apply Derivation.implicationIntroduction
  have hp := Derivation.hypothesis (body := SourcePresentation.sourceBody source context)
    (show ((literalTyped comp context (numeral (typeNumber .ground)) x ⊓ literalGround x) ⊓
      literalR source context x y) ∈ [((literalTyped comp context
        (numeral (typeNumber .ground)) x ⊓ literalGround x) ⊓ literalR source context x y)]
      from List.mem_cons_self)
  have htx := Derivation.conjunctionLeft (Derivation.conjunctionLeft hp)
  have hgx := Derivation.conjunctionRight (Derivation.conjunctionLeft hp)
  have hr := Derivation.conjunctionRight hp
  exact Derivation.conjunctionIntroduction
    (Derivation.implicationElimination (weakenClosed dt _)
      (Derivation.conjunctionIntroduction htx hr))
    (Derivation.implicationElimination (weakenClosed ds _)
      (Derivation.conjunctionIntroduction hgx hr))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceCompletionProof
