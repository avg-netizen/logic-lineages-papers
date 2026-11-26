module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalMachineFinishProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalAlgebraProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalMachineBinaryFinishProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalMachineState
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalAcceptanceBranchProof InternalPathCheckerBranchProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open OriginalLambdaConstructorGraphSyntaxProof OriginalLambdaTraversalInternalSubstitutionProof
open OriginalRawSyntaxTransportInternalMachineStateProof OriginalRawSyntaxTransportInternalConstructorSubstitutionProof
open OriginalStructuralNodeSizeInternalMachineFinishProof OriginalRawSyntaxTransportInternalConstructorSupportProof
open InternalTagArithmeticSyntaxProof (z suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {positive : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

def binaryInputs : Fin 3 → Program 1 :=
  ![succOf (addOf (headOf (tailOf results)) (headOf results)),rest,tailOf (tailOf results)]

theorem binarySubstitution :
    Substitutes (binaryInputs) returnState (OriginalStructuralNodeSize.returnedTwo) :=
  liveSubstitution (.projection 1) (consSubstitution (.projection 0) (.projection 2))

theorem binaryReturn
    (state raw suffix stack codedWork first second midStack resultSuffix produced out : OTerm alpha)
    (hs : Nonempty (Derivation positive Delta (OpenedFinish state raw suffix stack codedWork)))
    (ha : Nonempty (Derivation positive Delta (graph1 (arityOf (.projection 0)) (suc (suc z)) raw)))
    (hc : Nonempty (Derivation positive Delta (graph2 InternalListCodec.consCode stack second midStack)))
    (hm : Nonempty (Derivation positive Delta (graph2 InternalListCodec.consCode midStack first resultSuffix)))
    (hp : Nonempty (Derivation positive Delta (graph3 (OriginalStructuralNodeSizeInternalAlgebraProof.rebuild) produced raw first second)))
    (ho : Nonempty (Derivation positive Delta (graph3 returnState out produced suffix resultSuffix))) :
    Nonempty (Derivation positive Delta (graph1 (OriginalStructuralNodeSize.transition) out state)) := by
  let xs : Fin 1 → OTerm alpha := ![state]
  have payload := andLeft (andRight (andRight (andRight (andRight hs))))
  have hrest := andLeft (andRight (andRight (andRight (andRight (andRight hs)))))
  have hstack := andRight (andRight (andRight (andRight (andRight (andRight hs)))))
  have hd := InternalListCodecSupportProof.consDestruction stack second midStack hc
  have hmd := InternalListCodecSupportProof.consDestruction midStack first resultSuffix hm
  have hsecond := unaryValue InternalListCodec.headCode results second stack xs (andLeft hd) hstack
  have hmid := unaryValue InternalListCodec.tailCode results midStack stack xs (andLeft (andRight hd)) hstack
  have hfirst := unaryValue InternalListCodec.headCode (tailOf results) first midStack xs (andLeft hmd) hmid
  have hsuffix := unaryValue InternalListCodec.tailCode (tailOf results) resultSuffix midStack xs (andLeft (andRight hmd)) hmid
  have hproduced := OriginalStructuralNodeSizeInternalAlgebraProof.binaryAt
    (headOf (tailOf results)) (headOf results) xs raw first second produced ha hp hfirst hsecond
  have hr := (substitutionGraph (binarySubstitution) ![produced,suffix,resultSuffix] xs out
    (fun i => Fin.cases hproduced (Fin.cases hrest (Fin.cases hsuffix (fun a => Fin.elim0 a))) i)).mp ho
  have harity := arityValueAt framePayload (suc (suc z)) raw xs payload ha
  apply finishIntro state raw suffix stack codedWork out hs
  apply branchNumeralIntro 2 1 (arityOf framePayload) _ _ out xs harity
  apply branchNumeralIntro 2 2 (arityOf framePayload) _ _ out xs harity
  apply nonzeroBranchIntro _ _ _ out stack xs hstack (andRight (andRight hd))
  exact nonzeroBranchIntro _ _ _ out midStack xs hmid (andRight (andRight hmd)) hr

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalMachineBinaryFinishProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalMachineBinaryFinishProof
