module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackCompositionStateProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendFrameQueryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackVisitProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackReturnLeafProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackReturnFinishProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendRunProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultStackReturnSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultStackVisitProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultStackEmptyProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultStackCompositionFrameSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationResultStack InternalApplicationResultStackComposition
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof InternalApplicationStepPeelComponentsProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalAcceptanceBranchProof
open InternalAcceptanceConjunctionProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open InternalTagArithmeticSupportProof InternalGraphCompositionFunctionalityProof
open InternalApplicationResultStackCompositionStateProof InternalApplicationResultStackReturnSupportProof
open InternalApplicationValidityStackAppendListProof InternalApplicationValidityStackAppendFrameQueryProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalParameterizedApplicationResultStack InternalParameterizedApplicationResultStackWiringProof
open InternalParameterizedApplicationResultStackReturnSupportProof (liveInner)
open InternalApplicationResultStackCompositionFrameSupportProof (currentFields)
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- A malformed frame fails; no claim is made about any other state. -/
theorem malformedFailure (guard leaf : Program 2) (combine : Program 5)
    (parameter : OTerm α)
    (state stack results frame tail tag value : OTerm α)
    (hs : Nonempty (Derivation body Gamma (graph2 liveState state stack results)))
    (hc : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode stack frame tail)))
    (hp : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing frame tag value)))
    (hz : Nonempty (Derivation body Gamma (graph2 InternalEqualityTest.equalityTest z tag z)))
    (h1 : Nonempty (Derivation body Gamma (graph2 InternalEqualityTest.equalityTest z tag (suc z)))) :
    Nonempty (Derivation body Gamma (graph2 (transitionP guard leaf combine) z state parameter)) := by
  let ss : Fin 1 → OTerm α := Fin.cons state Fin.elim0
  let xs : Fin 2 → OTerm α := Fin.cons state (Fin.cons parameter Fin.elim0)
  have ht := andLeft (andRight (andRight (currentFields state stack results frame tail tag value hs hc hp)))
  apply liveInner guard leaf combine state stack results frame tail z parameter hs hc
  apply zeroBranchIntro _ _ _ z xs
    (liftValue _ z state parameter (binaryValue InternalEqualityTest.equalityTest frameTag (InternalAcceptance.constantZero 1)
      z tag z ss hz ht (constantZeroValue ss)))
  exact zeroBranchIntro _ _ _ z xs
    (liftValue _ z state parameter (binaryValue InternalEqualityTest.equalityTest frameTag (InternalLessThan.constantOne 1)
      z tag (suc z) ss h1 ht (InternalLessThanSupportProof.oneConstantValue ss))) (constantZeroValue xs)

/-- Finish underflow with no result is an actual zero transition. -/
theorem emptyResultsFailure (guard leaf : Program 2) (combine : Program 5)
    (parameter : OTerm α)
    (state stack frame tail tag value : OTerm α)
    (hs : Nonempty (Derivation body Gamma (graph2 liveState state stack z)))
    (hc : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode stack frame tail)))
    (hp : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing frame tag value)))
    (hz : Nonempty (Derivation body Gamma (graph2 InternalEqualityTest.equalityTest z tag z)))
    (h1 : Nonempty (Derivation body Gamma (graph2 InternalEqualityTest.equalityTest (suc z) tag (suc z)))) :
    Nonempty (Derivation body Gamma (graph2 (transitionP guard leaf combine) z state parameter)) := by
  let ss : Fin 1 → OTerm α := Fin.cons state Fin.elim0
  let xs : Fin 2 → OTerm α := Fin.cons state (Fin.cons parameter Fin.elim0)
  have ht := andLeft (andRight (andRight (currentFields state stack z frame tail tag value hs hc hp)))
  apply liveInner guard leaf combine state stack z frame tail z parameter hs hc
  apply zeroBranchIntro _ _ _ z xs
    (liftValue _ z state parameter (binaryValue InternalEqualityTest.equalityTest frameTag (InternalAcceptance.constantZero 1)
      z tag z ss hz ht (constantZeroValue ss)))
  apply successorBranchIntro _ _ _ z z xs
    (liftValue _ (suc z) state parameter (binaryValue InternalEqualityTest.equalityTest frameTag (InternalLessThan.constantOne 1)
      (suc z) tag (suc z) ss h1 ht (InternalLessThanSupportProof.oneConstantValue ss)))
  exact zeroBranchIntro _ _ _ z xs (liftValue _ z state parameter (andRight (liveStateFields state stack z hs))) (constantZeroValue xs)

/-- Finish underflow with exactly one result is an actual zero transition. -/
theorem singletonResultsFailure (guard leaf : Program 2) (combine : Program 5)
    (parameter : OTerm α)
    (state stack results frame tail tag value argument : OTerm α)
    (hs : Nonempty (Derivation body Gamma (graph2 liveState state stack results)))
    (hc : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode stack frame tail)))
    (hp : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing frame tag value)))
    (hr : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode results argument z)))
    (hz : Nonempty (Derivation body Gamma (graph2 InternalEqualityTest.equalityTest z tag z)))
    (h1 : Nonempty (Derivation body Gamma (graph2 InternalEqualityTest.equalityTest (suc z) tag (suc z)))) :
    Nonempty (Derivation body Gamma (graph2 (transitionP guard leaf combine) z state parameter)) := by
  let ss : Fin 1 → OTerm α := Fin.cons state Fin.elim0
  let xs : Fin 2 → OTerm α := Fin.cons state (Fin.cons parameter Fin.elim0)
  have ht := andLeft (andRight (andRight (currentFields state stack results frame tail tag value hs hc hp)))
  have hres := andRight (liveStateFields state stack results hs)
  have hd := InternalListCodecSupportProof.consDestruction results argument z hr
  apply liveInner guard leaf combine state stack results frame tail z parameter hs hc
  apply zeroBranchIntro _ _ _ z xs
    (liftValue _ z state parameter (binaryValue InternalEqualityTest.equalityTest frameTag (InternalAcceptance.constantZero 1)
      z tag z ss hz ht (constantZeroValue ss)))
  apply successorBranchIntro _ _ _ z z xs
    (liftValue _ (suc z) state parameter (binaryValue InternalEqualityTest.equalityTest frameTag (InternalLessThan.constantOne 1)
      (suc z) tag (suc z) ss h1 ht (InternalLessThanSupportProof.oneConstantValue ss)))
  apply nonzeroBranchIntro _ _ _ z results xs (liftValue _ results state parameter hres)
    (by simpa only [equalEqn] using andRight (andRight hd))
  exact zeroBranchIntro _ _ _ z xs
    (liftValue _ z state parameter (unaryValue InternalListCodec.tailCode InternalApplicationResultStack.results z results ss
      (andLeft (andRight hd)) hres)) (constantZeroValue xs)

theorem leafTransitionAt (guard leaf : Program 2) (combine : Program 5)
    (parameter : OTerm α)
    (state stack results frame value tail out leafValue nextResults : OTerm α)
    (hs : Nonempty (Derivation body Gamma (graph2 liveState state stack results)))
    (hc : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode stack frame tail)))
    (hp : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing frame z value)))
    (hg : Nonempty (Derivation body Gamma (graph2 (openGuardP guard) z value parameter)))
    (hl : Nonempty (Derivation body Gamma (graph2 leaf leafValue value parameter)))
    (hn : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode nextResults leafValue results)))
    (ho : Nonempty (Derivation body Gamma (graph2 liveState out tail nextResults))) :
    Nonempty (Derivation body Gamma (graph2 (transitionP guard leaf combine) out state parameter)) := by
  exact InternalParameterizedApplicationResultStackReturnSupportProof.leafAt guard leaf combine
    state stack results frame value tail out parameter leafValue hs hc hp hg hl
    (InternalApplicationResultStackCompositionFrameConstructorsProof.returnStateAt out tail results leafValue nextResults ho hn)

theorem finishTransitionAt (guard leaf : Program 2) (combine : Program 5)
    (parameter : OTerm α)
    (state stack results frame value d e tail argument function remaining afterArgument out combinedValue nextResults : OTerm α)
    (hs : Nonempty (Derivation body Gamma (graph2 liveState state stack results)))
    (hc : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode stack frame tail)))
    (hp : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing frame (suc z) value)))
    (hv : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing value d e)))
    (hr : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode results argument afterArgument)))
    (ht : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode afterArgument function remaining)))
    (hcomb : Nonempty (Derivation body Gamma (programGraph combine combinedValue (Fin.cons d (Fin.cons e (Fin.cons function (Fin.cons argument (Fin.cons parameter Fin.elim0))))))))
    (hn : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode nextResults combinedValue remaining)))
    (ho : Nonempty (Derivation body Gamma (graph2 liveState out tail nextResults))) :
    Nonempty (Derivation body Gamma (graph2 (transitionP guard leaf combine) out state parameter)) := by
  exact InternalParameterizedApplicationResultStackReturnSupportProof.finishAt guard leaf combine
    state stack results frame value d e tail argument function remaining afterArgument out parameter combinedValue
    hs hc hp hv hr ht hcomb
    (InternalApplicationResultStackCompositionFrameConstructorsProof.returnStateAt out tail remaining combinedValue nextResults ho hn)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultStackCompositionFrameSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultStackCompositionFrameSupportProof
