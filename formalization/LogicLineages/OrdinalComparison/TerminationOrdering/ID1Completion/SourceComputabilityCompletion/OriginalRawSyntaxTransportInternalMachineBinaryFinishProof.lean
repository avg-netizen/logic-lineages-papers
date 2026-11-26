module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalMachineFinishProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalMachineBinaryFinishProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalMachineState
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalAcceptanceBranchProof InternalPathCheckerBranchProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open OriginalLambdaConstructorGraphSyntaxProof OriginalLambdaTraversalInternalSubstitutionProof
open OriginalRawSyntaxTransportInternalMachineStateProof OriginalRawSyntaxTransportInternalConstructorSubstitutionProof
open OriginalRawSyntaxTransportInternalMachineFinishProof OriginalRawSyntaxTransportInternalConstructorSupportProof
open InternalTagArithmeticSyntaxProof (z suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {positive : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

def binaryInputs (mode : Mode) : Fin 3 → Program 1 :=
  ![.composition (rebuild mode) ![framePayload,headOf (tailOf results),headOf results],rest,tailOf (tailOf results)]

theorem binarySubstitution (mode : Mode) :
    Substitutes (binaryInputs mode) returnState (returnedTwo mode) :=
  liveSubstitution (.projection 1) (consSubstitution (.projection 0) (.projection 2))

theorem binaryReturn (mode : Mode)
    (state raw suffix stack codedWork first second midStack resultSuffix produced out : OTerm alpha)
    (hs : Nonempty (Derivation positive Delta (OpenedFinish state raw suffix stack codedWork)))
    (ha : Nonempty (Derivation positive Delta (graph1 (arityOf (.projection 0)) (suc (suc z)) raw)))
    (hc : Nonempty (Derivation positive Delta (graph2 InternalListCodec.consCode stack second midStack)))
    (hm : Nonempty (Derivation positive Delta (graph2 InternalListCodec.consCode midStack first resultSuffix)))
    (hp : Nonempty (Derivation positive Delta (graph3 (rebuild mode) produced raw first second)))
    (ho : Nonempty (Derivation positive Delta (graph3 returnState out produced suffix resultSuffix))) :
    Nonempty (Derivation positive Delta (graph1 (transition mode) out state)) := by
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
  have hproduced := compositionValue (rebuild mode) ![framePayload,headOf (tailOf results),headOf results]
    produced xs ![raw,first,second] hp (fun i => Fin.cases payload (Fin.cases hfirst
      (Fin.cases hsecond (fun a => Fin.elim0 a))) i)
  have hr := (substitutionGraph (binarySubstitution mode) ![produced,suffix,resultSuffix] xs out
    (fun i => Fin.cases hproduced (Fin.cases hrest (Fin.cases hsuffix (fun a => Fin.elim0 a))) i)).mp ho
  have harity := arityValueAt framePayload (suc (suc z)) raw xs payload ha
  apply finishIntro mode state raw suffix stack codedWork out hs
  apply branchNumeralIntro 2 1 (arityOf framePayload) _ _ out xs harity
  apply branchNumeralIntro 2 2 (arityOf framePayload) _ _ out xs harity
  apply nonzeroBranchIntro _ _ _ out stack xs hstack (andRight (andRight hd))
  exact nonzeroBranchIntro _ _ _ out midStack xs hmid (andRight (andRight hmd)) hr

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalMachineBinaryFinishProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalMachineBinaryFinishProof
