module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationCertifiedResultFoldClosureTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultStackCompositionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackCompositionFrameConstructorsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultStackVisitProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertifiedResultFoldClosureApplicationCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertifiedResultFoldClosureFuelProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationCertifiedResultFoldClosureApplicationCoreProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertifiedResultFoldClosure
open InternalApplicationResultStackComposition (liveState)
open InternalParameterizedApplicationResultStackCompositionSyntaxProof
open InternalParameterizedApplicationResultStackCompositionProof
open InternalParameterizedApplicationResultStackCompositionRunProof
open InternalParameterizedApplicationResultStackCompositionFrameSupportProof
open InternalParameterizedApplicationResultStackCompositionBasicProof InternalParameterizedApplicationResultStackCompositionStepProof
open InternalApplicationResultStackCompositionStateProof InternalApplicationResultStackCompositionFrameConstructorsProof
open InternalApplicationValidityStackAppendListProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalApplicationStepPeelSupportProof
open InternalAcceptanceConjunctionProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

open InternalPairingSumBounds InternalOriginalOrderSyntaxProof InternalUnpairReverseSyntaxProof
open InternalUnpairReverseBoundsArithmeticProof InternalSourceInversionSupportProof

/-- Contextual consumer of the exact output-preserving work composition. -/
theorem workAppend {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}
    (guard leaf : Program 2) (combine : Program 5) (parameter : OrdinaryArithmetic.Term α)
    (first second frontWork suffix joined initialResults middleResults finalResults : OrdinaryArithmetic.Term α)
    (ha : Nonempty (Derivation body Gamma
      (graph2 InternalApplicationValidityStackAppend.append joined frontWork suffix)))
    (hf : Nonempty (Derivation body Gamma
      (run guard leaf combine parameter first frontWork initialResults middleResults)))
    (hs : Nonempty (Derivation body Gamma
      (run guard leaf combine parameter second suffix middleResults finalResults))) :
    Nonempty (Derivation body Gamma (run guard leaf combine parameter
      (OrdinaryArithmetic.addTerm first second) joined initialResults finalResults)) :=
  InternalParameterizedApplicationResultStackCompositionInductionCoreProof.workRowApply guard leaf combine parameter
    first second frontWork suffix joined initialResults middleResults finalResults
    (InternalParameterizedApplicationResultStackCompositionWorkProof.allRows guard leaf combine parameter first) ha hf hs

/-- Contextual consumer retaining the entire appended result background. -/
theorem resultSuffixFrame {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}
    (guard leaf : Program 2) (combine : Program 5) (parameter : OrdinaryArithmetic.Term α)
    (count work initialResults finalResults background framedInitial framedFinal : OrdinaryArithmetic.Term α)
    (hr : Nonempty (Derivation body Gamma
      (run guard leaf combine parameter count work initialResults finalResults)))
    (hi : Nonempty (Derivation body Gamma
      (graph2 InternalApplicationValidityStackAppend.append framedInitial initialResults background)))
    (hf : Nonempty (Derivation body Gamma
      (graph2 InternalApplicationValidityStackAppend.append framedFinal finalResults background))) :
    Nonempty (Derivation body Gamma (run guard leaf combine parameter count work framedInitial framedFinal)) :=
  InternalParameterizedApplicationResultStackCompositionInductionCoreProof.resultRowApply guard leaf combine parameter
    count work initialResults finalResults background framedInitial framedFinal
    (InternalParameterizedApplicationResultStackCompositionResultProof.allRows guard leaf combine parameter count) hr hi hf

theorem runAtBound (guard leaf : Program 2) (combine : Program 5) (parameter : OTerm α)
    (count fuel work initialResults finalResults : OTerm α)
    (hb : Nonempty (Derivation body Gamma (weakBound count fuel)))
    (hr : Nonempty (Derivation body Gamma (run guard leaf combine parameter count work initialResults finalResults))) :
    Nonempty (Derivation body Gamma (run guard leaf combine parameter fuel work initialResults finalResults)) := by
  apply weakOrderCases Gamma count fuel _ hb
  intro β j Delta padding hj he
  rw [actualRunRename]
  have hr' := renameInto hr j Delta hj
  rw [actualRunRename] at hr'
  exact countTransport guard leaf combine (parameter.relabel j) (OrdinaryArithmetic.addTerm (count.relabel j) padding) (fuel.relabel j)
    (work.relabel j) (initialResults.relabel j) (finalResults.relabel j) he
    (runPadding guard leaf combine (parameter.relabel j) (count.relabel j) padding (work.relabel j)
      (initialResults.relabel j) (finalResults.relabel j) hr')

/-- Actual runs are composed with their complete result stacks. No assertion
is made about an untouched work suffix after either child's padded count. -/
theorem applicationRun (guard leaf : Program 2) (combine : Program 5) (parameter : OTerm α)
    (d e fp ap arrow fn arg parent functionOut argumentOut out first second
      functionVisit argumentVisit parentVisit types finish
      functionWork argumentWork parentWork finishWork argumentFinish expandedWork
      functionResults argumentResults bothResults outputResults
      parentState expandedState finishState outputState : OTerm α)
    (harrow : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode arrow d e)))
    (hfn : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing fn arrow fp)))
    (harg : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing arg d ap)))
    (hparent : Nonempty (Derivation body Gamma (graph4 packedApplication parent d e fp ap)))
    (hguard : Nonempty (Derivation body Gamma (graph2 guard (suc z) parent parameter)))
    (hcombine : Nonempty (Derivation body Gamma (programGraph combine out (Fin.cons d (Fin.cons e (Fin.cons functionOut (Fin.cons argumentOut (Fin.cons parameter Fin.elim0))))))))
    (hfv : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing functionVisit z fn)))
    (hav : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing argumentVisit z arg)))
    (hpv : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing parentVisit z parent)))
    (hty : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing types d e)))
    (hfinish : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing finish (suc z) types)))
    (hfw : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode functionWork functionVisit z)))
    (haw : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode argumentWork argumentVisit z)))
    (hpw : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode parentWork parentVisit z)))
    (hfinishw : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode finishWork finish z)))
    (hafw : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode argumentFinish argumentVisit finishWork)))
    (hew : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode expandedWork functionVisit argumentFinish)))
    (hfr : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode functionResults functionOut z)))
    (har : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode argumentResults argumentOut z)))
    (hbr : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode bothResults argumentOut functionResults)))
    (hor : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode outputResults out z)))
    (hps : Nonempty (Derivation body Gamma (graph2 liveState parentState parentWork z)))
    (hes : Nonempty (Derivation body Gamma (graph2 liveState expandedState expandedWork z)))
    (hfs : Nonempty (Derivation body Gamma (graph2 liveState finishState finishWork bothResults)))
    (hos : Nonempty (Derivation body Gamma (graph2 liveState outputState z outputResults)))
    (hrf : Nonempty (Derivation body Gamma (run guard leaf combine parameter first functionWork z functionResults)))
    (hra : Nonempty (Derivation body Gamma (run guard leaf combine parameter second argumentWork z argumentResults))) :
    Nonempty (Derivation body Gamma (run guard leaf combine parameter
      (suc (OrdinaryArithmetic.addTerm first (OrdinaryArithmetic.addTerm second (suc z))))
      parentWork z outputResults)) := by
  have hframed := resultSuffixFrame guard leaf combine parameter second argumentWork z argumentResults
    functionResults functionResults bothResults hra (appendZeroValue functionResults)
    (consBackward argumentResults argumentOut z functionResults functionResults bothResults
      har (appendZeroValue functionResults) hbr)
  have hfinishStep := finishTransitionAt guard leaf combine parameter finishState finishWork bothResults
    finish types d e z argumentOut functionOut z functionResults outputState out outputResults
    hfs hfinishw hfinish hty hbr hfr hcombine hor hos
  have hfinishRun := runFrontBackward guard leaf combine parameter z finishWork bothResults outputResults
    finishState z outputResults outputState hfs hos hfinishStep
    (emptyRun guard leaf combine parameter z outputResults)
  have hargumentFinish := workAppend guard leaf combine parameter second (suc z)
    argumentWork finishWork argumentFinish functionResults bothResults outputResults
    (consBackward argumentWork argumentVisit z finishWork finishWork argumentFinish
      haw (appendZeroValue finishWork) hafw) hframed hfinishRun
  have hchildren := workAppend guard leaf combine parameter first (OrdinaryArithmetic.addTerm second (suc z))
    functionWork argumentFinish expandedWork z functionResults outputResults
    (consBackward functionWork functionVisit z argumentFinish argumentFinish expandedWork
      hfw (appendZeroValue argumentFinish) hew) hrf hargumentFinish
  have hopen := InternalParameterizedApplicationResultStackVisitProof.visitBackward guard leaf combine
    d e fp ap parent z z parentState expandedState parameter hparent
    (visitStateAt parentState parentWork z parentVisit parent z hps hpw hpv) hguard
    (expandedStateAt expandedState expandedWork z d e fp ap z arrow fn arg
      functionVisit argumentVisit types finish finishWork argumentFinish
      hes harrow hfn harg hfv hav hty hfinish hfinishw hafw hew)
  exact runFrontBackward guard leaf combine parameter
    (OrdinaryArithmetic.addTerm first (OrdinaryArithmetic.addTerm second (suc z)))
    parentWork z outputResults parentState expandedWork z expandedState hps hes hopen hchildren

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationCertifiedResultFoldClosureApplicationCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationCertifiedResultFoldClosureApplicationCoreProof
