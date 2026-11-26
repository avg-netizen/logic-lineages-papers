module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalVisitSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalBranchProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalLambdaTraversal OriginalLambdaTraversalInternal
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalAcceptanceBranchProof InternalPathCheckerBranchProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalLambdaConstructorGraphSyntaxProof OriginalLambdaTraversalInternalVisitSyntaxProof
open OriginalHereditaryValidityInternalNodeSupportProof (exactAccept)
open OriginalHereditaryValidityInternalBranchProof (sameRejectAt oneNotTwo)
open InternalApplicationStepPeelSupportProof (sameAccept)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {positive : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

def visitDispatch (leaf : Program 2) : Program 1 :=
  InternalAcceptance.branch (InternalApplicationStepPeel.same currentTag (two 1))
    (InternalAcceptance.branch (OriginalHereditaryValidity.exactOne currentTag)
      (leafReturned leaf) lambdaExpanded) applicationExpanded

theorem dispatchIntro (leaf : Program 2) (state value parameter suffix stack codedWork out : OTerm alpha)
    (h : Nonempty (Derivation positive Delta (OpenedVisit state value parameter suffix stack codedWork)))
    (hd : Nonempty (Derivation positive Delta (graph1 (visitDispatch leaf) out state))) :
    Nonempty (Derivation positive Delta (graph1 (transition leaf) out state)) := by
  let xs : Fin 1 → OTerm alpha := Fin.cons state Fin.elim0
  apply successorBranchIntro _ _ _ out z xs (exactAccept status xs (andLeft h))
  apply nonzeroBranchIntro _ _ _ out codedWork xs (andLeft (andRight h)) (andLeft (andRight (andRight h)))
  exact successorBranchIntro _ _ _ out z xs
    (sameAccept frameTag (InternalAcceptance.constantZero 1) z xs
      (andLeft (andRight (andRight (andRight h)))) (InternalLessThanSupportProof.zeroConstantValue xs)) hd

theorem dispatchElim (leaf : Program 2) (state value parameter suffix stack codedWork out : OTerm alpha)
    (h : Nonempty (Derivation positive Delta (OpenedVisit state value parameter suffix stack codedWork)))
    (ho : Nonempty (Derivation positive Delta (graph1 (transition leaf) out state))) :
    Nonempty (Derivation positive Delta (graph1 (visitDispatch leaf) out state)) := by
  let xs : Fin 1 → OTerm alpha := Fin.cons state Fin.elim0
  have hs := successorBranchElim _ _ _ out z xs (exactAccept status xs (andLeft h)) ho
  have hw := nonzeroBranchElim _ _ _ out codedWork xs (andLeft (andRight h))
    (andLeft (andRight (andRight h))) hs
  exact successorBranchElim _ _ _ out z xs
    (sameAccept frameTag (InternalAcceptance.constantZero 1) z xs
      (andLeft (andRight (andRight (andRight h)))) (InternalLessThanSupportProof.zeroConstantValue xs)) hw

theorem applicationIntro (leaf : Program 2) (state out : OTerm alpha)
    (ht : Nonempty (Derivation positive Delta (graph1 currentTag (numeral 2) state)))
    (ho : Nonempty (Derivation positive Delta (graph1 applicationExpanded out state))) :
    Nonempty (Derivation positive Delta (graph1 (visitDispatch leaf) out state)) :=
  successorBranchIntro _ _ _ out z (Fin.cons state Fin.elim0)
    (sameAccept currentTag (two 1) (numeral 2) (Fin.cons state Fin.elim0) ht (twoValue _)) ho

theorem applicationElim (leaf : Program 2) (state out : OTerm alpha)
    (ht : Nonempty (Derivation positive Delta (graph1 currentTag (numeral 2) state)))
    (ho : Nonempty (Derivation positive Delta (graph1 (visitDispatch leaf) out state))) :
    Nonempty (Derivation positive Delta (graph1 applicationExpanded out state)) :=
  successorBranchElim _ _ _ out z (Fin.cons state Fin.elim0)
    (sameAccept currentTag (two 1) (numeral 2) (Fin.cons state Fin.elim0) ht (twoValue _)) ho

theorem lambdaIntro (leaf : Program 2) (state out : OTerm alpha)
    (ht : Nonempty (Derivation positive Delta (graph1 currentTag (numeral 1) state)))
    (ho : Nonempty (Derivation positive Delta (graph1 lambdaExpanded out state))) :
    Nonempty (Derivation positive Delta (graph1 (visitDispatch leaf) out state)) := by
  let xs : Fin 1 → OTerm alpha := Fin.cons state Fin.elim0
  apply zeroBranchIntro _ _ _ out xs
    (sameRejectAt currentTag (two 1) (numeral 1) (numeral 2) xs ht (twoValue xs) oneNotTwo)
  exact successorBranchIntro _ _ _ out z xs (exactAccept currentTag xs ht) ho

theorem lambdaElim (leaf : Program 2) (state out : OTerm alpha)
    (ht : Nonempty (Derivation positive Delta (graph1 currentTag (numeral 1) state)))
    (ho : Nonempty (Derivation positive Delta (graph1 (visitDispatch leaf) out state))) :
    Nonempty (Derivation positive Delta (graph1 lambdaExpanded out state)) := by
  let xs : Fin 1 → OTerm alpha := Fin.cons state Fin.elim0
  have hz := zeroBranchElim _ _ _ out xs
    (sameRejectAt currentTag (two 1) (numeral 1) (numeral 2) xs ht (twoValue xs) oneNotTwo) ho
  exact successorBranchElim _ _ _ out z xs (exactAccept currentTag xs ht) hz

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalBranchProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalBranchProof
