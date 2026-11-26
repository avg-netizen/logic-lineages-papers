module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAgendaPotentialFrameProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSquareRootArithmeticSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAgendaPotentialReturnProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof
open InternalAdditionLawsProof (add leftSuccessor leftZero)
open InternalSquareRootArithmeticSupportProof (orderRight)

theorem actualReturnPop : OriginalHereditaryAgendaPotentialTargets.ReturnPop := by
 intro body alpha Delta frame payload work rest branching before after hf hc hb ha
 have hcost := OriginalHereditaryAgendaPotentialFrameProof.returnCost frame payload branching hf
 obtain ⟨he⟩ := OriginalHereditaryAgendaPotentialRecurrenceProof.consEquation
   work frame rest branching (suc z) after before hc hcost ha hb
 have hsum : Derivation body Delta (eqn (add (suc z) after) (suc after)) :=
   trans (leftSuccessor z after) (congSuc (leftZero after))
 exact ⟨orderRight after (symm (trans he hsum))
   (InternalQuotientComparisonProof.equalToNext (refl after))⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAgendaPotentialReturnProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAgendaPotentialReturnProof
