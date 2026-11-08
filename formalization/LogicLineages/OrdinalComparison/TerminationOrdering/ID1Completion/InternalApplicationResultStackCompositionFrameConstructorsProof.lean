module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackCompositionFrameSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackCompositionFrameConstructorsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationResultStack InternalApplicationResultStackComposition
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof InternalApplicationStepPeelComponentsProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalAcceptanceBranchProof
open InternalAcceptanceConjunctionProof InternalAcceptanceNormalizationProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open InternalTagArithmeticSupportProof InternalGraphCompositionFunctionalityProof
open InternalApplicationResultStackCompositionStateProof InternalApplicationResultStackReturnSupportProof
open InternalApplicationResultStackReturnRelationProof
open InternalApplicationValidityStackAppendListProof InternalApplicationValidityStackAppendFrameQueryProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem visitStateAt (state stack results frame value tail : OTerm α)
    (hs : Nonempty (Derivation body Gamma (graph2 liveState state stack results)))
    (hc : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode stack frame tail)))
    (hp : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing frame z value))) :
    Nonempty (Derivation body Gamma (graph3 visitState state value tail results)) := by
  let xs : Fin 3 → OTerm α := Fin.cons value (Fin.cons tail (Fin.cons results Fin.elim0))
  have hv := binaryValue InternalPairing.pairing (InternalAcceptance.constantZero 3) (.projection 0)
    frame z value xs hp (constantZeroValue xs) (projectionValue 0 xs)
  have hw := binaryValue InternalListCodec.consCode (visitOf (.projection 0)) (.projection 1)
    stack frame tail xs hc hv (projectionValue 1 xs)
  exact liveOfValue _ _ state stack results xs hs hw (projectionValue 2 xs)

theorem returnStateAt (state stack results value extended : OTerm α)
    (hs : Nonempty (Derivation body Gamma (graph2 liveState state stack extended)))
    (hc : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode extended value results))) :
    Nonempty (Derivation body Gamma (graph3 returnState state value stack results)) := by
  let xs : Fin 3 → OTerm α := Fin.cons value (Fin.cons stack (Fin.cons results Fin.elim0))
  exact liveOfValue _ _ state stack extended xs hs (projectionValue 1 xs)
    (binaryValue InternalListCodec.consCode (.projection 0) (.projection 2)
      extended value results xs hc (projectionValue 0 xs) (projectionValue 2 xs))

theorem finishStateAt (state stack results frame value d e tail argument function remaining afterArgument : OTerm α)
    (hs : Nonempty (Derivation body Gamma (graph2 liveState state stack results)))
    (hc : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode stack frame tail)))
    (hp : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing frame (suc z) value)))
    (hv : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing value d e)))
    (hr : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode results argument afterArgument)))
    (ht : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode afterArgument function remaining))) :
    Nonempty (Derivation body Gamma (graph6 finishState state d e tail argument function remaining)) := by
  let xs : Fin 6 → OTerm α := Fin.cons d (Fin.cons e (Fin.cons tail
    (Fin.cons argument (Fin.cons function (Fin.cons remaining Fin.elim0)))))
  have hv' := binaryValue InternalPairing.pairing (.projection 0) (.projection 1)
    value d e xs hv (projectionValue 0 xs) (projectionValue 1 xs)
  have hf := binaryValue InternalPairing.pairing (InternalLessThan.constantOne 6)
    (pairOf (.projection 0) (.projection 1)) frame (suc z) value xs hp
    (InternalLessThanSupportProof.oneConstantValue xs) hv'
  have hw := binaryValue InternalListCodec.consCode (finishOf (.projection 0) (.projection 1))
    (.projection 2) stack frame tail xs hc hf (projectionValue 2 xs)
  have ht' := binaryValue InternalListCodec.consCode (.projection 4) (.projection 5)
    afterArgument function remaining xs ht (projectionValue 4 xs) (projectionValue 5 xs)
  have hr' := binaryValue InternalListCodec.consCode (.projection 3) (consOf (.projection 4) (.projection 5))
    results argument afterArgument xs hr (projectionValue 3 xs) ht'
  exact liveOfValue _ _ state stack results xs hs hw hr'

theorem expandedStateAt (state stack results d e fp ap tail arrow function argument functionVisit argumentVisit
    types finish finishWork argumentWork : OTerm α)
    (hs : Nonempty (Derivation body Gamma (graph2 liveState state stack results)))
    (har : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode arrow d e)))
    (hf : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing function arrow fp)))
    (ha : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing argument d ap)))
    (hfv : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing functionVisit z function)))
    (hav : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing argumentVisit z argument)))
    (hty : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing types d e)))
    (hfin : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing finish (suc z) types)))
    (hfw : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode finishWork finish tail)))
    (haw : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode argumentWork argumentVisit finishWork)))
    (hew : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode stack functionVisit argumentWork))) :
    Nonempty (Derivation body Gamma (graph6 expandedState state d e fp ap tail results)) := by
  let xs : Fin 6 → OTerm α := Fin.cons d (Fin.cons e (Fin.cons fp (Fin.cons ap (Fin.cons tail (Fin.cons results Fin.elim0)))))
  have har' := binaryValue InternalListCodec.consCode (.projection 0) (.projection 1)
    arrow d e xs har (projectionValue 0 xs) (projectionValue 1 xs)
  have hf' := binaryValue InternalPairing.pairing (consOf (.projection 0) (.projection 1)) (.projection 2)
    function arrow fp xs hf har' (projectionValue 2 xs)
  have ha' := binaryValue InternalPairing.pairing (.projection 0) (.projection 3)
    argument d ap xs ha (projectionValue 0 xs) (projectionValue 3 xs)
  have hfv' := binaryValue InternalPairing.pairing (InternalAcceptance.constantZero 6)
    (pairOf (consOf (.projection 0) (.projection 1)) (.projection 2))
    functionVisit z function xs hfv (constantZeroValue xs) hf'
  have hav' := binaryValue InternalPairing.pairing (InternalAcceptance.constantZero 6)
    (pairOf (.projection 0) (.projection 3)) argumentVisit z argument xs hav (constantZeroValue xs) ha'
  have hty' := binaryValue InternalPairing.pairing (.projection 0) (.projection 1)
    types d e xs hty (projectionValue 0 xs) (projectionValue 1 xs)
  have hfin' := binaryValue InternalPairing.pairing (InternalLessThan.constantOne 6)
    (pairOf (.projection 0) (.projection 1)) finish (suc z) types xs hfin
    (InternalLessThanSupportProof.oneConstantValue xs) hty'
  have hfw' := binaryValue InternalListCodec.consCode (finishOf (.projection 0) (.projection 1))
    (.projection 4) finishWork finish tail xs hfw hfin' (projectionValue 4 xs)
  have haw' := binaryValue InternalListCodec.consCode (visitOf (pairOf (.projection 0) (.projection 3)))
    (consOf (finishOf (.projection 0) (.projection 1)) (.projection 4)) argumentWork argumentVisit finishWork xs haw hav' hfw'
  have hew' := binaryValue InternalListCodec.consCode
    (visitOf (pairOf (consOf (.projection 0) (.projection 1)) (.projection 2)))
    (consOf (visitOf (pairOf (.projection 0) (.projection 3)))
      (consOf (finishOf (.projection 0) (.projection 1)) (.projection 4))) stack functionVisit argumentWork xs hew hfv' haw'
  exact liveOfValue _ _ state stack results xs hs hew' (projectionValue 5 xs)

theorem leafTransitionAt (guard leaf : Program 1) (combine : Program 4)
    (state stack results frame value tail out leafValue nextResults : OTerm α)
    (hs : Nonempty (Derivation body Gamma (graph2 liveState state stack results)))
    (hc : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode stack frame tail)))
    (hp : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing frame z value)))
    (hg : Nonempty (Derivation body Gamma (graph1 (openGuard guard) z value)))
    (hl : Nonempty (Derivation body Gamma (graph1 leaf leafValue value)))
    (hn : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode nextResults leafValue results)))
    (ho : Nonempty (Derivation body Gamma (graph2 liveState out tail nextResults))) :
    Nonempty (Derivation body Gamma (graph1 (transition guard leaf combine) out state)) := by
  apply InternalApplicationResultStackReturnLeafProof.leafBackward guard leaf combine
    value tail results state out (visitStateAt state stack results frame value tail hs hc hp) hg
  rw [leafResultEqReturned]
  exact returnedIntro leaf out (Fin.cons value Fin.elim0) tail results leafValue hl
    (returnStateAt out tail results leafValue nextResults ho hn)

theorem finishTransitionAt (guard leaf : Program 1) (combine : Program 4)
    (state stack results frame value d e tail argument function remaining afterArgument out combinedValue nextResults : OTerm α)
    (hs : Nonempty (Derivation body Gamma (graph2 liveState state stack results)))
    (hc : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode stack frame tail)))
    (hp : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing frame (suc z) value)))
    (hv : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing value d e)))
    (hr : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode results argument afterArgument)))
    (ht : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode afterArgument function remaining)))
    (hcomb : Nonempty (Derivation body Gamma (graph4 combine combinedValue d e function argument)))
    (hn : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode nextResults combinedValue remaining)))
    (ho : Nonempty (Derivation body Gamma (graph2 liveState out tail nextResults))) :
    Nonempty (Derivation body Gamma (graph1 (transition guard leaf combine) out state)) := by
  apply InternalApplicationResultStackReturnFinishProof.finishBackward guard leaf combine
    d e tail argument function remaining state out
    (finishStateAt state stack results frame value d e tail argument function remaining afterArgument hs hc hp hv hr ht)
  rw [finishResultEqReturned]
  exact returnedIntro combine out (Fin.cons d (Fin.cons e (Fin.cons function (Fin.cons argument Fin.elim0))))
    tail remaining combinedValue hcomb (returnStateAt out tail remaining combinedValue nextResults ho hn)

theorem zeroGraphNotOne {n : Nat} (p : Program n) (xs : Fin n → OTerm α)
    (hp : Nonempty (Derivation body Gamma (programGraph p z xs))) :
    Nonempty (Derivation body Gamma (programGraph p (suc z) xs).not) := by
  obtain ⟨h⟩ := valueUnique p (suc z) z xs
    (show Nonempty (Derivation body (programGraph p (suc z) xs :: Gamma) (programGraph p (suc z) xs)) from
      ⟨Derivation.hypothesis List.mem_cons_self⟩) (InternalApplicationValidityStackAppendFrameQueryProof.weakenProof hp
        (fun _ h => List.mem_cons_of_mem _ h))
  exact ⟨Derivation.implicationIntroduction (sucNeZeroApply h)⟩

theorem conjunctionRejectLeft {n : Nat} (p q : Program n) (xs : Fin n → OTerm α)
    (hp : Nonempty (Derivation body Gamma (programGraph p z xs))) :
    Nonempty (Derivation body Gamma (programGraph (InternalAcceptance.conjunction p q) z xs)) :=
  zeroBranchIntro _ _ _ z xs (normalizeReject p xs (zeroGraphNotOne p xs hp)) (constantZeroValue xs)

theorem conjunctionRejectRight {n : Nat} (p q : Program n) (xs : Fin n → OTerm α)
    (hp : Nonempty (Derivation body Gamma (programGraph p (suc z) xs)))
    (hq : Nonempty (Derivation body Gamma (programGraph q (suc z) xs).not)) :
    Nonempty (Derivation body Gamma (programGraph (InternalAcceptance.conjunction p q) z xs)) :=
  successorBranchIntro _ _ _ z z xs (normalizeAccept p xs hp) (normalizeReject q xs hq)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackCompositionFrameConstructorsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackCompositionFrameConstructorsProof
