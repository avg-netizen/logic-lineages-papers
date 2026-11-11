module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalMachineVisitProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalMachineBranchProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalMachineState
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalAcceptanceBranchProof InternalPathCheckerBranchProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalLambdaConstructorGraphSyntaxProof OriginalRawSyntaxTransportInternalMachineVisitProof
open OriginalHereditaryValidityInternalNodeSupportProof (exactAccept)
open OriginalHereditaryValidityInternalBranchProof (sameRejectAt oneNotTwo)
open InternalApplicationStepPeelSupportProof (sameAccept)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {positive : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

def visitDispatch (mode : Mode) : Program 1 :=
  InternalAcceptance.branch (sameOf (arityOf currentRaw) (constant 1 1))
    (InternalAcceptance.branch (sameOf (arityOf currentRaw) (constant 1 2))
      (leafReturned mode) expandedTwo) expandedOne

theorem dispatchIntro (mode : Mode) (state d k value suffix stack codedWork out : OTerm alpha)
    (h : Nonempty (Derivation positive Delta (OpenedVisit state d k value suffix stack codedWork)))
    (hd : Nonempty (Derivation positive Delta (graph1 (visitDispatch mode) out state))) :
    Nonempty (Derivation positive Delta (graph1 (transition mode) out state)) := by
  let xs : Fin 1 → OTerm alpha := Fin.cons state Fin.elim0
  apply successorBranchIntro _ _ _ out z xs (exactAccept status xs (andLeft h))
  apply nonzeroBranchIntro _ _ _ out codedWork xs (andLeft (andRight h)) (andLeft (andRight (andRight h)))
  exact successorBranchIntro _ _ _ out z xs
    (sameAccept frameTag (InternalAcceptance.constantZero 1) z xs
      (andLeft (andRight (andRight (andRight h)))) (InternalLessThanSupportProof.zeroConstantValue xs)) hd

theorem dispatchElim (mode : Mode) (state d k value suffix stack codedWork out : OTerm alpha)
    (h : Nonempty (Derivation positive Delta (OpenedVisit state d k value suffix stack codedWork)))
    (ho : Nonempty (Derivation positive Delta (graph1 (transition mode) out state))) :
    Nonempty (Derivation positive Delta (graph1 (visitDispatch mode) out state)) := by
  let xs : Fin 1 → OTerm alpha := Fin.cons state Fin.elim0
  have hs := successorBranchElim _ _ _ out z xs (exactAccept status xs (andLeft h)) ho
  have hw := nonzeroBranchElim _ _ _ out codedWork xs (andLeft (andRight h))
    (andLeft (andRight (andRight h))) hs
  exact successorBranchElim _ _ _ out z xs
    (sameAccept frameTag (InternalAcceptance.constantZero 1) z xs
      (andLeft (andRight (andRight (andRight h)))) (InternalLessThanSupportProof.zeroConstantValue xs)) hw

theorem zeroNotSuccessor (x : OTerm alpha) :
    Nonempty (Derivation positive Delta (equal z (suc x)).not) := by
  have h : Derivation positive [equal z (suc x)] (eqn z (suc x)) := by
    simpa only [equalEqn] using
      (Derivation.hypothesis List.mem_cons_self : Derivation positive [equal z (suc x)] (equal z (suc x)))
  exact ⟨InternalPositiveUnfoldingSupportProof.weakenClosed
    (Derivation.implicationIntroduction (InternalTagArithmeticSupportProof.zeroNeSuc h)) Delta⟩

theorem leafIntro (mode : Mode) (state out : OTerm alpha)
    (ha : Nonempty (Derivation positive Delta (graph1 (arityOf currentRaw) z state)))
    (ho : Nonempty (Derivation positive Delta (graph1 (leafReturned mode) out state))) :
    Nonempty (Derivation positive Delta (graph1 (visitDispatch mode) out state)) := by
  let xs : Fin 1 → OTerm alpha := Fin.cons state Fin.elim0
  apply zeroBranchIntro _ _ _ out xs
    (sameRejectAt (arityOf currentRaw) (constant 1 1) z (suc z) xs ha
      (InternalLessThanSupportProof.oneConstantValue xs) (zeroNotSuccessor z))
  exact zeroBranchIntro _ _ _ out xs
    (sameRejectAt (arityOf currentRaw) (constant 1 2) z (suc (suc z)) xs ha
      (twoValue xs) (zeroNotSuccessor (suc z))) ho

theorem leafElim (mode : Mode) (state out : OTerm alpha)
    (ha : Nonempty (Derivation positive Delta (graph1 (arityOf currentRaw) z state)))
    (ho : Nonempty (Derivation positive Delta (graph1 (visitDispatch mode) out state))) :
    Nonempty (Derivation positive Delta (graph1 (leafReturned mode) out state)) := by
  let xs : Fin 1 → OTerm alpha := Fin.cons state Fin.elim0
  have h1 := zeroBranchElim _ _ _ out xs
    (sameRejectAt (arityOf currentRaw) (constant 1 1) z (suc z) xs ha
      (InternalLessThanSupportProof.oneConstantValue xs) (zeroNotSuccessor z)) ho
  exact zeroBranchElim _ _ _ out xs
    (sameRejectAt (arityOf currentRaw) (constant 1 2) z (suc (suc z)) xs ha
      (twoValue xs) (zeroNotSuccessor (suc z))) h1

theorem unaryIntro (mode : Mode) (state out : OTerm alpha)
    (ha : Nonempty (Derivation positive Delta (graph1 (arityOf currentRaw) (suc z) state)))
    (ho : Nonempty (Derivation positive Delta (graph1 expandedOne out state))) :
    Nonempty (Derivation positive Delta (graph1 (visitDispatch mode) out state)) :=
  successorBranchIntro _ _ _ out z (Fin.cons state Fin.elim0)
    (sameAccept (arityOf currentRaw) (constant 1 1) (suc z) (Fin.cons state Fin.elim0)
      ha (InternalLessThanSupportProof.oneConstantValue _)) ho

theorem unaryElim (mode : Mode) (state out : OTerm alpha)
    (ha : Nonempty (Derivation positive Delta (graph1 (arityOf currentRaw) (suc z) state)))
    (ho : Nonempty (Derivation positive Delta (graph1 (visitDispatch mode) out state))) :
    Nonempty (Derivation positive Delta (graph1 expandedOne out state)) :=
  successorBranchElim _ _ _ out z (Fin.cons state Fin.elim0)
    (sameAccept (arityOf currentRaw) (constant 1 1) (suc z) (Fin.cons state Fin.elim0)
      ha (InternalLessThanSupportProof.oneConstantValue _)) ho

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalMachineBranchProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalMachineBranchProof
