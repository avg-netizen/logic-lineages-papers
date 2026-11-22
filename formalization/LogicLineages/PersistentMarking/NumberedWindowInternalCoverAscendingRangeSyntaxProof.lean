module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAscendingRangeTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionLawsProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverAscendingRangeSyntaxProof
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
open NumberedWindowInternalCoverAscendingRangeTargets

theorem testRename {α β : Type} (bound i : OTerm α) (j : α → β) :
    (rangeTest bound i).relabel j = rangeTest (bound.relabel j) (i.relabel j) := by
  simp only [rangeTest,programRename,binaryInputsRename,sucRelabel,zRelabel]

theorem atRename {α β : Type} (bound i : OTerm α) (j : α → β) :
    (atBound bound i).relabel j = atBound (bound.relabel j) (i.relabel j) := by
  change ((ID1Completion.InternalOriginalOrderSyntaxProof.ltF i bound).relabel j).imp
    ((rangeTest bound i).relabel j) = _
  rw [orderRename,testRename]

private theorem testSubst {α β : Type} (bound i : OTerm α) (ts : α → OTerm β) :
    (rangeTest bound i).subst (fun a => emb (ts a)) =
      rangeTest (bound.subst ts) (i.subst ts) := by
  have tape : (fun k => ((![bound,i] : Fin 2 → OTerm α) k).subst ts) = ![bound.subst ts,i.subst ts] := by
    funext k
    exact Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)) k
  unfold rangeTest
  rw [programSubst,tape,sucSubst,zSubst]

theorem atSubst {α β : Type} (bound i : OTerm α) (ts : α → OTerm β) :
    (atBound bound i).subst (fun a => emb (ts a)) = atBound (bound.subst ts) (i.subst ts) := by
  simp only [atBound,impSubst,orderSubst,testSubst]

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverAscendingRangeSyntaxProof
