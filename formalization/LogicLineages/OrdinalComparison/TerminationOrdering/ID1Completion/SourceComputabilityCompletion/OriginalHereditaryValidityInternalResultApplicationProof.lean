module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalResultSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFiniteBlocksProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalResultApplicationProof
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
open OriginalHereditaryValidityInternalResultSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open OriginalLambdaConstructorGraphSyntaxProof InternalGraphCompositionFunctionalityProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem applicationForward (state out parameter restCode : InternalGraphComposition.OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph1 currentParameter parameter state)))
    (hr : Nonempty (Derivation body Delta (graph1 rest restCode state)))
    (h : Nonempty (Derivation body Delta (graph1 applicationExpanded out state))) :
    Nonempty (Derivation body Delta (ApplicationResult state out parameter restCode)) := by
  let ff := pairOf currentFunction currentParameter
  let af := pairOf currentArgument currentParameter
  let suffix := consOf af rest
  let workCode := consOf ff suffix
  let qs : Fin 6 → Program 1 := ![currentFunction,currentArgument,ff,af,suffix,workCode]
  let xs : Fin 1 → InternalGraphComposition.OTerm alpha := Fin.cons state Fin.elim0
  apply queryCases qs xs _
  intro beta j ys Theta hj hq
  rw [applicationResultRename]
  have hp' := renameInto hp j Theta hj
  have hr' := renameInto hr j Theta hj
  have h' := renameInto h j Theta hj
  rw [graph1Rename] at hp' hr' h'
  simp only [xs,consTermRename,emptyRename] at hq
  let xx : Fin 1 → InternalGraphComposition.OTerm beta := Fin.cons (state.relabel j) Fin.elim0
  have hf := binaryRecover InternalPairing.pairing currentFunction currentParameter
    (ys 2) (ys 0) (parameter.relabel j) xx (hq 2) (hq 0) hp'
  have ha := binaryRecover InternalPairing.pairing currentArgument currentParameter
    (ys 3) (ys 1) (parameter.relabel j) xx (hq 3) (hq 1) hp'
  have ht := binaryRecover InternalListCodec.consCode af rest
    (ys 4) (ys 3) (restCode.relabel j) xx (hq 4) (hq 3) hr'
  have hw := binaryRecover InternalListCodec.consCode ff suffix
    (ys 5) (ys 2) (ys 4) xx (hq 5) (hq 2) (hq 4)
  have ho := binaryRecover InternalPairing.pairing (InternalLessThan.constantOne 1) workCode
    (out.relabel j) (numeral 1) (ys 5) xx h'
    (InternalLessThanSupportProof.oneConstantValue xx) (hq 5)
  exact applicationResultIntro _ _ _ _ (ys 0) (ys 1)
    (andIntro (hq 0) (andIntro (hq 1)
      (pushedApplicationIntro _ _ _ _ _ (ys 5) (ys 4) (ys 2) (ys 3)
        (andIntro ho (andIntro hw (andIntro hf (andIntro ht ha)))))))

theorem applicationBackward (state out parameter restCode : InternalGraphComposition.OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph1 currentParameter parameter state)))
    (hr : Nonempty (Derivation body Delta (graph1 rest restCode state)))
    (h : Nonempty (Derivation body Delta (ApplicationResult state out parameter restCode))) :
    Nonempty (Derivation body Delta (graph1 applicationExpanded out state)) := by
  apply applicationResultCases state out parameter restCode _ h
  intro beta j Theta fn arg hj hv
  rw [graph1Rename]
  have hp' := renameInto hp j Theta hj
  have hr' := renameInto hr j Theta hj
  rw [graph1Rename] at hp' hr'
  have hf := andLeft hv
  have ha := andLeft (andRight hv)
  have hpushed := andRight (andRight hv)
  apply pushedApplicationCases (out.relabel j) fn arg (parameter.relabel j) (restCode.relabel j) _ hpushed
  intro gamma k Xi workCode suffix fnFrame argFrame hk fields
  rw [graph1Rename]
  have hp'' := renameInto hp' k Xi hk
  have hr'' := renameInto hr' k Xi hk
  have hf' := renameInto hf k Xi hk
  have ha' := renameInto ha k Xi hk
  rw [graph1Rename] at hp'' hr'' hf' ha'
  let xx : Fin 1 → InternalGraphComposition.OTerm gamma := Fin.cons ((state.relabel j).relabel k) Fin.elim0
  have hff := binaryValue InternalPairing.pairing currentFunction currentParameter
    fnFrame (fn.relabel k) ((parameter.relabel j).relabel k) xx
    (andLeft (andRight (andRight fields))) hf' hp''
  have haf := binaryValue InternalPairing.pairing currentArgument currentParameter
    argFrame (arg.relabel k) ((parameter.relabel j).relabel k) xx
    (andRight (andRight (andRight (andRight fields)))) ha' hp''
  have ht := binaryValue InternalListCodec.consCode (pairOf currentArgument currentParameter) rest
    suffix argFrame ((restCode.relabel j).relabel k) xx
    (andLeft (andRight (andRight (andRight fields)))) haf hr''
  have hw := binaryValue InternalListCodec.consCode (pairOf currentFunction currentParameter)
    (consOf (pairOf currentArgument currentParameter) rest) workCode fnFrame suffix xx
    (andLeft (andRight fields)) hff ht
  exact binaryValue InternalPairing.pairing (InternalLessThan.constantOne 1)
    (consOf (pairOf currentFunction currentParameter)
      (consOf (pairOf currentArgument currentParameter) rest))
    ((out.relabel j).relabel k) (numeral 1) workCode xx (andLeft fields)
    (InternalLessThanSupportProof.oneConstantValue xx) hw

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalResultApplicationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalResultApplicationProof
