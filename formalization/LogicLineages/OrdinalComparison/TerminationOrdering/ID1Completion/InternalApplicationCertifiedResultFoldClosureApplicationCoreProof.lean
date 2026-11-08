module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertifiedResultFoldClosureTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackCompositionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackCompositionFrameConstructorsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackVisitProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertifiedResultFoldClosureApplicationCoreProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertifiedResultFoldClosure
open InternalApplicationResultStackComposition InternalApplicationResultStackCompositionProof
open InternalApplicationResultStackCompositionBasicProof InternalApplicationResultStackCompositionStepProof
open InternalApplicationResultStackCompositionStateProof InternalApplicationResultStackCompositionFrameConstructorsProof
open InternalApplicationValidityStackAppendListProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalApplicationStepPeelSupportProof
open InternalAcceptanceConjunctionProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem visitWorkAt (work frame value : OTerm α)
    (hf : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing frame z value)))
    (hw : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode work frame z))) :
    Nonempty (Derivation body Gamma (graph1 visitWork work value)) := by
  let xs : Fin 1 → OTerm α := Fin.cons value Fin.elim0
  have hv := binaryValue InternalPairing.pairing (InternalAcceptance.constantZero 1)
    (.projection 0) frame z value xs hf (constantZeroValue xs) (projectionValue 0 xs)
  exact binaryValue InternalListCodec.consCode
    (InternalApplicationResultStack.visitOf (.projection 0)) (InternalAcceptance.constantZero 1)
    work frame z xs hw hv (constantZeroValue xs)

/-- Actual runs are composed with their complete result stacks. No assertion
is made about an untouched work suffix after either child's padded count. -/
theorem applicationRun (guard leaf : Program 1) (combine : Program 4)
    (d e fp ap arrow fn arg parent functionOut argumentOut out first second
      functionVisit argumentVisit parentVisit types finish
      functionWork argumentWork parentWork finishWork argumentFinish expandedWork
      functionResults argumentResults bothResults outputResults
      parentState expandedState finishState outputState : OTerm α)
    (harrow : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode arrow d e)))
    (hfn : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing fn arrow fp)))
    (harg : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing arg d ap)))
    (hparent : Nonempty (Derivation body Gamma (graph4 packedApplication parent d e fp ap)))
    (hguard : Nonempty (Derivation body Gamma (graph1 guard (suc z) parent)))
    (hcombine : Nonempty (Derivation body Gamma (graph4 combine out d e functionOut argumentOut)))
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
    (hrf : Nonempty (Derivation body Gamma (actualRun guard leaf combine first functionWork z functionResults)))
    (hra : Nonempty (Derivation body Gamma (actualRun guard leaf combine second argumentWork z argumentResults))) :
    Nonempty (Derivation body Gamma (actualRun guard leaf combine
      (suc (OrdinaryArithmetic.addTerm first (OrdinaryArithmetic.addTerm second (suc z))))
      parentWork z outputResults)) := by
  have hframed := resultSuffixFrame guard leaf combine second argumentWork z argumentResults
    functionResults functionResults bothResults hra (appendZeroValue functionResults)
    (consBackward argumentResults argumentOut z functionResults functionResults bothResults
      har (appendZeroValue functionResults) hbr)
  have hfinishStep := finishTransitionAt guard leaf combine finishState finishWork bothResults
    finish types d e z argumentOut functionOut z functionResults outputState out outputResults
    hfs hfinishw hfinish hty hbr hfr hcombine hor hos
  have hfinishRun := runFrontBackward guard leaf combine z finishWork bothResults outputResults
    finishState z outputResults outputState hfs hos hfinishStep
    (emptyRun guard leaf combine z outputResults)
  have hargumentFinish := workAppend guard leaf combine second (suc z)
    argumentWork finishWork argumentFinish functionResults bothResults outputResults
    (consBackward argumentWork argumentVisit z finishWork finishWork argumentFinish
      haw (appendZeroValue finishWork) hafw) hframed hfinishRun
  have hchildren := workAppend guard leaf combine first (OrdinaryArithmetic.addTerm second (suc z))
    functionWork argumentFinish expandedWork z functionResults outputResults
    (consBackward functionWork functionVisit z argumentFinish argumentFinish expandedWork
      hfw (appendZeroValue argumentFinish) hew) hrf hargumentFinish
  have hopen := InternalApplicationResultStackVisitProof.visitBackward guard leaf combine
    d e fp ap parent z z parentState expandedState hparent
    (visitStateAt parentState parentWork z parentVisit parent z hps hpw hpv) hguard
    (expandedStateAt expandedState expandedWork z d e fp ap z arrow fn arg
      functionVisit argumentVisit types finish finishWork argumentFinish
      hes harrow hfn harg hfv hav hty hfinish hfinishw hafw hew)
  exact runFrontBackward guard leaf combine
    (OrdinaryArithmetic.addTerm first (OrdinaryArithmetic.addTerm second (suc z)))
    parentWork z outputResults parentState expandedWork z expandedState hps hes hopen hchildren

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertifiedResultFoldClosureApplicationCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertifiedResultFoldClosureApplicationCoreProof
