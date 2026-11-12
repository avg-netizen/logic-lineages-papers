module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalMachineStateProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalMachineBranchProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorSubstitutionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalAlgebraProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalMachineFinishProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalMachineState
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalAcceptanceBranchProof InternalPathCheckerBranchProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open OriginalLambdaConstructorGraphSyntaxProof OriginalLambdaTraversalInternalSubstitutionProof
open OriginalRawSyntaxTransportInternalMachineStateProof OriginalRawSyntaxTransportInternalConstructorSubstitutionProof
open InternalApplicationResultStackCompositionStateProof (liveStateFields liveStatus)
open InternalApplicationResultStackComposition (liveState)
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open InternalApplicationStepPeelSupportProof (sameAccept)
open OriginalHereditaryValidityInternalBranchProof (sameRejectAt)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {positive : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

def OpenedFinish (state raw suffix stack codedWork : OTerm alpha) : Formula alpha :=
  graph1 status (suc z) state ⊓ (graph1 work codedWork state ⊓
    ((eqn codedWork z).not ⊓ (graph1 frameTag (suc z) state ⊓
      (graph1 framePayload raw state ⊓ (graph1 rest suffix state ⊓ graph1 results stack state)))))

@[simp] theorem openedFinishRename {beta : Type}
    (state raw suffix stack codedWork : OTerm alpha) (j : alpha → beta) :
    (OpenedFinish state raw suffix stack codedWork).relabel j =
      OpenedFinish (state.relabel j) (raw.relabel j) (suffix.relabel j) (stack.relabel j) (codedWork.relabel j) := by
  simp only [OpenedFinish,conjunctionRename,graph1Rename,
    OriginalRawSyntaxTransportInternalMachineVisitProof.negationRename,
    InternalTagArithmeticSyntaxProof.eqnRelabel,sucRelabel,zRelabel]

theorem openedFinish (state raw suffix stack frameCode codedWork : OTerm alpha)
    (hf : Nonempty (Derivation positive Delta (graph1 finishFrame frameCode raw)))
    (hw : Nonempty (Derivation positive Delta (graph2 InternalListCodec.consCode codedWork frameCode suffix)))
    (hs : Nonempty (Derivation positive Delta (graph2 liveState state codedWork stack))) :
    Nonempty (Derivation positive Delta (OpenedFinish state raw suffix stack codedWork)) := by
  let xs : Fin 1 → OTerm alpha := ![state]
  have hp := binaryRecover InternalPairing.pairing (constant 1 1) (.projection 0)
    frameCode (suc z) raw ![raw] hf (InternalLessThanSupportProof.oneConstantValue _) (projectionValue 0 ![raw])
  have fields := liveStateFields state codedWork stack hs
  have hstatus := liveStatus state codedWork stack hs
  have hwork := andLeft fields
  have hresults := andRight fields
  have hc := InternalListCodecSupportProof.consDestruction codedWork frameCode suffix hw
  have hframe : Nonempty (Derivation positive Delta (graph1 frame frameCode state)) :=
    unaryValue InternalListCodec.headCode work frameCode codedWork xs (andLeft hc) hwork
  have hrest : Nonempty (Derivation positive Delta (graph1 rest suffix state)) :=
    unaryValue InternalListCodec.tailCode work suffix codedWork xs (andLeft (andRight hc)) hwork
  have htag : Nonempty (Derivation positive Delta (graph1 frameTag (suc z) state)) :=
    unaryValue InternalUnpair.left frame (suc z) frameCode xs (pairLeft frameCode (suc z) raw hp) hframe
  have hpayload : Nonempty (Derivation positive Delta (graph1 framePayload raw state)) :=
    unaryValue InternalUnpair.right frame raw frameCode xs (pairRight frameCode (suc z) raw hp) hframe
  exact andIntro hstatus (andIntro hwork (andIntro (andRight (andRight hc))
    (andIntro htag (andIntro hpayload (andIntro hrest hresults)))))

def finishDispatch : Program 1 :=
  InternalAcceptance.branch (sameOf (arityOf framePayload) (constant 1 1))
    (InternalAcceptance.branch (sameOf (arityOf framePayload) (constant 1 2)) (constant 1 0)
      (InternalAcceptance.branch results (constant 1 0)
        (InternalAcceptance.branch (tailOf results) (constant 1 0) (OriginalStructuralNodeSize.returnedTwo))))
    (InternalAcceptance.branch results (constant 1 0) (OriginalStructuralNodeSize.returnedOne))

theorem finishIntro (state raw suffix stack codedWork out : OTerm alpha)
    (h : Nonempty (Derivation positive Delta (OpenedFinish state raw suffix stack codedWork)))
    (hd : Nonempty (Derivation positive Delta (graph1 (finishDispatch) out state))) :
    Nonempty (Derivation positive Delta (graph1 (OriginalStructuralNodeSize.transition) out state)) := by
  let xs : Fin 1 → OTerm alpha := ![state]
  have ht := andLeft (andRight (andRight (andRight h)))
  have hz := binaryValue InternalEqualityTest.equalityTest frameTag (constant 1 0)
    z (suc z) z xs
    (InternalEqualityTestCompositionProof.rejectBackwardGap (suc z) z z
      ⟨InternalAdditionLawsProof.leftZero (suc z)⟩)
    ht (InternalLessThanSupportProof.zeroConstantValue xs)
  apply successorBranchIntro _ _ _ out z xs
    (sameAccept status (constant 1 1) (suc z) xs (andLeft h) (InternalLessThanSupportProof.oneConstantValue xs))
  apply nonzeroBranchIntro _ _ _ out codedWork xs (andLeft (andRight h)) (andLeft (andRight (andRight h)))
  apply zeroBranchIntro _ _ _ out xs hz
  exact successorBranchIntro _ _ _ out z xs
    (sameAccept frameTag (constant 1 1) (suc z) xs ht (InternalLessThanSupportProof.oneConstantValue xs)) hd

def unaryInputs : Fin 3 → Program 1 :=
  ![succOf (headOf results),rest,tailOf results]

theorem unarySubstitution :
    Substitutes (unaryInputs) returnState (OriginalStructuralNodeSize.returnedOne) :=
  liveSubstitution (.projection 1) (consSubstitution (.projection 0) (.projection 2))

theorem unaryReturn
    (state raw suffix stack codedWork first resultSuffix produced out : OTerm alpha)
    (hs : Nonempty (Derivation positive Delta (OpenedFinish state raw suffix stack codedWork)))
    (ha : Nonempty (Derivation positive Delta (graph1 (arityOf (.projection 0)) (suc z) raw)))
    (hc : Nonempty (Derivation positive Delta (graph2 InternalListCodec.consCode stack first resultSuffix)))
    (hp : Nonempty (Derivation positive Delta (graph3 (OriginalStructuralNodeSizeInternalAlgebraProof.rebuild) produced raw first z)))
    (ho : Nonempty (Derivation positive Delta (graph3 returnState out produced suffix resultSuffix))) :
    Nonempty (Derivation positive Delta (graph1 (OriginalStructuralNodeSize.transition) out state)) := by
  let xs : Fin 1 → OTerm alpha := ![state]
  have payload := andLeft (andRight (andRight (andRight (andRight hs))))
  have hrest := andLeft (andRight (andRight (andRight (andRight (andRight hs)))))
  have hstack := andRight (andRight (andRight (andRight (andRight (andRight hs)))))
  have hd := InternalListCodecSupportProof.consDestruction stack first resultSuffix hc
  have hfirst := unaryValue InternalListCodec.headCode results first stack xs (andLeft hd) hstack
  have hsuffix := unaryValue InternalListCodec.tailCode results resultSuffix stack xs (andLeft (andRight hd)) hstack
  have hproduced := unaryValue .succ (headOf results) produced first xs
    (OriginalStructuralNodeSizeInternalAlgebraProof.unaryRecover raw first z produced ha hp) hfirst
  have hr := (substitutionGraph (unarySubstitution) ![produced,suffix,resultSuffix] xs out
    (fun i => Fin.cases hproduced (Fin.cases hrest (Fin.cases hsuffix (fun a => Fin.elim0 a))) i)).mp ho
  apply finishIntro state raw suffix stack codedWork out hs
  apply successorBranchIntro _ _ _ out z xs
    (sameAccept (arityOf framePayload) (constant 1 1) (suc z) xs
      (arityValueAt framePayload (suc z) raw xs payload ha) (InternalLessThanSupportProof.oneConstantValue xs))
  exact nonzeroBranchIntro _ _ _ out stack xs hstack (andRight (andRight hd)) hr

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalMachineFinishProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalMachineFinishProof
