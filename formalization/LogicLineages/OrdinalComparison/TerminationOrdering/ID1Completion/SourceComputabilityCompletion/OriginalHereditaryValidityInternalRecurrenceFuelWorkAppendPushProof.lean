module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelAppendInductionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalPushSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelWorkAppendPushProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalHereditaryValidityInternal OriginalHereditaryValidityInternalPushSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

def appFnFrame : Program 5 := pairOf (.projection 0) (.projection 2)
def appArgFrame : Program 5 := pairOf (.projection 1) (.projection 2)
def appFrontArg : Program 5 := consOf appArgFrame (.projection 3)
def appJoinedArg : Program 5 := consOf appArgFrame (.projection 4)
def appFrontWork : Program 5 := consOf appFnFrame appFrontArg
def appJoinedWork : Program 5 := consOf appFnFrame appJoinedArg
def appPushQueries : Fin 8 → Program 5 := ![appFnFrame,appArgFrame,appFrontArg,appJoinedArg,
  appFrontWork,appJoinedWork,pairOf (InternalLessThan.constantOne 5) appFrontWork,
  pairOf (InternalLessThan.constantOne 5) appJoinedWork]

 theorem applicationPushCases (fn arg parameter frontRest joinedRest suffix : OTerm alpha)
    (psi : Formula alpha)
    (ha : Nonempty (Derivation body Delta
      (graph2 InternalApplicationValidityStackAppend.append joinedRest frontRest suffix)))
    (k : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
      (frontWork joinedWork frontState joinedState : OTerm beta),
      (∀ p ∈ Delta, p.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta
        (graph2 InternalApplicationValidityStackAppend.append joinedWork frontWork (suffix.relabel j))) →
      Nonempty (Derivation body Theta (StateGraph frontState (numeral 1) frontWork)) →
      Nonempty (Derivation body Theta (StateGraph joinedState (numeral 1) joinedWork)) →
      Nonempty (Derivation body Theta (PushedApplication frontState (fn.relabel j) (arg.relabel j)
        (parameter.relabel j) (frontRest.relabel j))) →
      Nonempty (Derivation body Theta (PushedApplication joinedState (fn.relabel j) (arg.relabel j)
        (parameter.relabel j) (joinedRest.relabel j))) →
      Nonempty (Derivation body Theta (psi.relabel j))) : Nonempty (Derivation body Delta psi) := by
  let xs : Fin 5 → OTerm alpha := Fin.cons fn (Fin.cons arg
    (Fin.cons parameter (Fin.cons frontRest (Fin.cons joinedRest Fin.elim0))))
  apply queryCases appPushQueries xs psi
  intro beta j ys Theta hj hq
  simp only [xs,consTermRename,emptyRename] at hq
  have ha' := renameInto ha j Theta hj
  rw [graph2Rename] at ha'
  let xx : Fin 5 → OTerm beta := Fin.cons (fn.relabel j) (Fin.cons (arg.relabel j)
    (Fin.cons (parameter.relabel j) (Fin.cons (frontRest.relabel j) (Fin.cons (joinedRest.relabel j) Fin.elim0))))
  have hff := binaryRecover InternalPairing.pairing (.projection 0) (.projection 2)
    (ys 0) (fn.relabel j) (parameter.relabel j) xx (hq 0) (projectionValue 0 xx) (projectionValue 2 xx)
  have haf := binaryRecover InternalPairing.pairing (.projection 1) (.projection 2)
    (ys 1) (arg.relabel j) (parameter.relabel j) xx (hq 1) (projectionValue 1 xx) (projectionValue 2 xx)
  have hfa := binaryRecover InternalListCodec.consCode appArgFrame (.projection 3)
    (ys 2) (ys 1) (frontRest.relabel j) xx (hq 2) (hq 1) (projectionValue 3 xx)
  have hja := binaryRecover InternalListCodec.consCode appArgFrame (.projection 4)
    (ys 3) (ys 1) (joinedRest.relabel j) xx (hq 3) (hq 1) (projectionValue 4 xx)
  have hfw := binaryRecover InternalListCodec.consCode appFnFrame appFrontArg
    (ys 4) (ys 0) (ys 2) xx (hq 4) (hq 0) (hq 2)
  have hjw := binaryRecover InternalListCodec.consCode appFnFrame appJoinedArg
    (ys 5) (ys 0) (ys 3) xx (hq 5) (hq 0) (hq 3)
  have hfs := binaryRecover InternalPairing.pairing (InternalLessThan.constantOne 5) appFrontWork
    (ys 6) (numeral 1) (ys 4) xx (hq 6) (InternalLessThanSupportProof.oneConstantValue xx) (hq 4)
  have hjs := binaryRecover InternalPairing.pairing (InternalLessThan.constantOne 5) appJoinedWork
    (ys 7) (numeral 1) (ys 5) xx (hq 7) (InternalLessThanSupportProof.oneConstantValue xx) (hq 5)
  have haArg := InternalApplicationValidityStackAppendListProof.consBackward
    (ys 2) (ys 1) (frontRest.relabel j) (suffix.relabel j) (joinedRest.relabel j) (ys 3) hfa ha' hja
  have haWork := InternalApplicationValidityStackAppendListProof.consBackward
    (ys 4) (ys 0) (ys 2) (suffix.relabel j) (ys 3) (ys 5) hfw haArg hjw
  exact k beta j Theta (ys 4) (ys 5) (ys 6) (ys 7) hj haWork hfs hjs
    (pushedApplicationIntro (ys 6) (fn.relabel j) (arg.relabel j) (parameter.relabel j)
      (frontRest.relabel j) (ys 4) (ys 2) (ys 0) (ys 1)
      (andIntro hfs (andIntro hfw (andIntro hff (andIntro hfa haf)))))
    (pushedApplicationIntro (ys 7) (fn.relabel j) (arg.relabel j) (parameter.relabel j)
      (joinedRest.relabel j) (ys 5) (ys 3) (ys 0) (ys 1)
      (andIntro hjs (andIntro hjw (andIntro hff (andIntro hja haf)))))


end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelWorkAppendPushProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelWorkAppendPushProof
