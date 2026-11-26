module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalResultLambdaSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFiniteBlocksProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalResultLambdaProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalHereditaryValidityInternal
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalRecursionGraphStepSyntaxProof InternalTagArithmeticSyntaxProof
open InternalRawListRecursionSyntaxProof InternalGraphCompositionSyntaxProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open SourceComputabilityFormulaSupportProof (numeral)

open OriginalHereditaryValidityInternalPushSyntaxProof OriginalHereditaryValidity
open OriginalHereditaryValidityInternalResultLambdaSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open OriginalLambdaConstructorGraphSyntaxProof InternalGraphCompositionFunctionalityProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

open OriginalHereditaryValidityInternalExtensionProof
theorem lambdaForward (state out raw parameter restCode : InternalGraphComposition.OTerm alpha)
    (hraw : Nonempty (Derivation body Delta (graph1 currentRaw raw state)))
    (hp : Nonempty (Derivation body Delta (graph1 currentParameter parameter state)))
    (hr : Nonempty (Derivation body Delta (graph1 rest restCode state)))
    (h : Nonempty (Derivation body Delta (graph1 lambdaExpanded out state))) :
    Nonempty (Derivation body Delta (LambdaResult state out raw parameter restCode)) := by
  let frame := pairOf currentBody childParameter
  let workCode := consOf frame rest
  let qs : Fin 4 → Program 1 := ![currentBody,childParameter,frame,workCode]
  let xs : Fin 1 → InternalGraphComposition.OTerm alpha := Fin.cons state Fin.elim0
  apply queryCases qs xs _
  intro beta j ys Theta hj hq
  rw [lambdaResultRename]
  have hp' := renameInto hp j Theta hj
  have hr' := renameInto hr j Theta hj
  have hraw' := renameInto hraw j Theta hj
  have h' := renameInto h j Theta hj
  rw [graph1Rename] at hp' hr' hraw' h'
  simp only [xs,consTermRename,emptyRename] at hq
  let xx : Fin 1 → InternalGraphComposition.OTerm beta := Fin.cons (state.relabel j) Fin.elim0
  have hf := binaryRecover InternalPairing.pairing currentBody childParameter
    (ys 2) (ys 0) (ys 1) xx (hq 2) (hq 0) (hq 1)
  have hw := binaryRecover InternalListCodec.consCode frame rest
    (ys 3) (ys 2) (restCode.relabel j) xx (hq 3) (hq 2) hr'
  have ho := binaryRecover InternalPairing.pairing (InternalLessThan.constantOne 1) workCode
    (out.relabel j) (numeral 1) (ys 3) xx h'
    (InternalLessThanSupportProof.oneConstantValue xx) (hq 3)
  have he := childParameterExtension (state.relabel j) (raw.relabel j)
    (parameter.relabel j) (ys 1) hraw' hp' (hq 1)
  exact lambdaResultIntro _ _ _ _ _ (ys 0) (ys 1)
    (andIntro (hq 0) (andIntro he (andIntro (hq 1)
      (pushedFrameIntro _ _ _ _ (ys 3) (ys 2) (andIntro ho (andIntro hw hf))))))

theorem lambdaBackward (state out raw parameter restCode : InternalGraphComposition.OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph1 rest restCode state)))
    (h : Nonempty (Derivation body Delta (LambdaResult state out raw parameter restCode))) :
    Nonempty (Derivation body Delta (graph1 lambdaExpanded out state)) := by
  apply lambdaResultCases state out raw parameter restCode _ h
  intro beta j Theta child childParameterCode hj hv
  rw [graph1Rename]
  have hr' := renameInto hr j Theta hj
  rw [graph1Rename] at hr'
  have hc := andLeft hv
  have hp := andLeft (andRight (andRight hv))
  have hpushed := andRight (andRight (andRight hv))
  apply pushedFrameCases (out.relabel j) child childParameterCode (restCode.relabel j) _ hpushed
  intro gamma k Xi workCode frame hk fields
  rw [graph1Rename]
  have hr'' := renameInto hr' k Xi hk
  have hc' := renameInto hc k Xi hk
  have hp' := renameInto hp k Xi hk
  rw [graph1Rename] at hr'' hc' hp'
  let xx : Fin 1 → InternalGraphComposition.OTerm gamma := Fin.cons ((state.relabel j).relabel k) Fin.elim0
  have hf := binaryValue InternalPairing.pairing currentBody childParameter
    frame (child.relabel k) (childParameterCode.relabel k) xx
    (andRight (andRight fields)) hc' hp'
  have hw := binaryValue InternalListCodec.consCode (pairOf currentBody childParameter) rest
    workCode frame ((restCode.relabel j).relabel k) xx (andLeft (andRight fields)) hf hr''
  exact binaryValue InternalPairing.pairing (InternalLessThan.constantOne 1)
    (consOf (pairOf currentBody childParameter) rest)
    ((out.relabel j).relabel k) (numeral 1) workCode xx (andLeft fields)
    (InternalLessThanSupportProof.oneConstantValue xx) hw

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalResultLambdaProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalResultLambdaProof
