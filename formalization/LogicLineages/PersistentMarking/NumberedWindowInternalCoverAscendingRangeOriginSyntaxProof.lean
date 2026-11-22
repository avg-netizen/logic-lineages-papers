module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAscendingRangeOriginTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAscendingRangeSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionLawsProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverAscendingRangeOriginSyntaxProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalRawListRecursionSyntaxProof (programSubst)
open ID1Completion.InternalOriginalOrderSyntaxProof (orderRename)
open ID1Completion.InternalQuotientComparisonSyntaxProof (orderSubst)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb sucRelabel zRelabel sucSubst zSubst)
open ID1Completion.InternalAdditionLawsProof (impSubst)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename)
open NumberedWindowInternalCoverAscendingRangeTargets (rangeTest)
open NumberedWindowInternalCoverAscendingRangeSyntaxProof (testRename)
open NumberedWindowInternalCoverAscendingRangeOriginTargets

theorem backRename {α β : Type} (bound i : OTerm α) (j : α → β) :
    (backBound bound i).relabel j = backBound (bound.relabel j) (i.relabel j) := by
  change ((rangeTest bound i).relabel j).imp
    ((ID1Completion.InternalOriginalOrderSyntaxProof.ltF i bound).relabel j) = _
  rw [orderRename,testRename]

private theorem testSubst {α β : Type} (bound i : OTerm α) (ts : α → OTerm β) :
    (rangeTest bound i).subst (fun a => emb (ts a)) =
      rangeTest (bound.subst ts) (i.subst ts) := by
  have tape : (fun k => ((![bound,i] : Fin 2 → OTerm α) k).subst ts) = ![bound.subst ts,i.subst ts] := by
    funext k
    exact Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)) k
  unfold rangeTest
  rw [programSubst,tape,sucSubst,zSubst]

theorem backSubst {α β : Type} (bound i : OTerm α) (ts : α → OTerm β) :
    (backBound bound i).subst (fun a => emb (ts a)) = backBound (bound.subst ts) (i.subst ts) := by
  simp only [backBound,impSubst,orderSubst,testSubst]

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverAscendingRangeOriginSyntaxProof
