module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultStackWiringProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackCompositionFrameConstructorsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultStackReturnSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationResultStack InternalApplicationResultStackComposition
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalAcceptanceBranchProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open InternalGraphCompositionFunctionalityProof
open InternalApplicationResultStackCompositionStateProof InternalApplicationResultStackCompositionFrameSupportProof
open InternalApplicationResultStackCompositionFrameConstructorsProof
open InternalApplicationResultStackReturnSupportProof InternalApplicationResultStackReturnRelationProof
open InternalParameterizedApplicationResultStackWiringProof InternalParameterizedApplicationResultStackSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem visitStateCases (state value tail results : OTerm α) (psi : Formula α)
    (hs : Nonempty (Derivation body Gamma (graph3 visitState state value tail results)))
    (k : ∀ (β : Type) (j : α → β) (Delta : List (Formula β)) (frame stack : OTerm β),
      (∀ p ∈ Gamma, p.relabel j ∈ Delta) →
      Nonempty (Derivation body Delta (graph2 liveState (state.relabel j) stack (results.relabel j))) →
      Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode stack frame (tail.relabel j))) →
      Nonempty (Derivation body Delta (graph2 InternalPairing.pairing frame z (value.relabel j))) →
      Nonempty (Derivation body Delta (psi.relabel j))) :
    Nonempty (Derivation body Gamma psi) := by
  let qs : Fin 3 → Program 3 := ![InternalApplicationResultStackReturnLeafSupportProof.frameQ,
    InternalApplicationResultStackReturnLeafSupportProof.workQ,
    InternalApplicationResultStackReturnLeafSupportProof.oldPairQ]
  apply queryCases qs (Fin.cons value (Fin.cons tail (Fin.cons results Fin.elim0))) psi
  intro β j ys Delta hj hq
  simp only [consTermRename,emptyRename] at hq
  have hs' := renameInto hs j Delta hj
  rw [graph3Rename] at hs'
  let xs : Fin 3 → OTerm β := Fin.cons (value.relabel j) (Fin.cons (tail.relabel j) (Fin.cons (results.relabel j) Fin.elim0))
  have hf := binaryRecover InternalPairing.pairing (InternalAcceptance.constantZero 3) (.projection 0)
    (ys 0) z (value.relabel j) xs (hq 0) (InternalLessThanSupportProof.zeroConstantValue xs) (projectionValue 0 xs)
  have hw := binaryRecover InternalListCodec.consCode _ (.projection 1)
    (ys 1) (ys 0) (tail.relabel j) xs (hq 1) (hq 0) (projectionValue 1 xs)
  have hi := binaryRecover InternalPairing.pairing _ (.projection 2)
    (ys 2) (ys 1) (results.relabel j) xs (hq 2) (hq 1) (projectionValue 2 xs)
  have ho := binaryRecover InternalPairing.pairing (InternalLessThan.constantOne 3) _
    (state.relabel j) (suc z) (ys 2) xs hs' (InternalLessThanSupportProof.oneConstantValue xs) (hq 2)
  exact k β j Delta (ys 0) (ys 1) hj
    (liveStateValue (state.relabel j) (ys 2) (ys 1) (results.relabel j) hi ho) hw hf

theorem finishStateCases (state d e tail argument function remaining : OTerm α) (psi : Formula α)
    (hs : Nonempty (Derivation body Gamma (graph6 finishState state d e tail argument function remaining)))
    (k : ∀ (β : Type) (j : α → β) (Delta : List (Formula β)) (value frame stack afterArgument results : OTerm β),
      (∀ p ∈ Gamma, p.relabel j ∈ Delta) →
      Nonempty (Derivation body Delta (graph2 liveState (state.relabel j) stack results)) →
      Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode stack frame (tail.relabel j))) →
      Nonempty (Derivation body Delta (graph2 InternalPairing.pairing frame (suc z) value)) →
      Nonempty (Derivation body Delta (graph2 InternalPairing.pairing value (d.relabel j) (e.relabel j))) →
      Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode results (argument.relabel j) afterArgument)) →
      Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode afterArgument (function.relabel j) (remaining.relabel j))) →
      Nonempty (Derivation body Delta (psi.relabel j))) :
    Nonempty (Derivation body Gamma psi) := by
  let qs : Fin 6 → Program 6 := ![InternalApplicationResultStackReturnFinishSupportProof.typeQ,
    InternalApplicationResultStackReturnFinishSupportProof.frameQ,
    InternalApplicationResultStackReturnFinishSupportProof.workQ,
    InternalApplicationResultStackReturnFinishSupportProof.tailResultsQ,
    InternalApplicationResultStackReturnFinishSupportProof.resultsQ,
    InternalApplicationResultStackReturnFinishSupportProof.oldPairQ]
  apply queryCases qs (Fin.cons d (Fin.cons e (Fin.cons tail (Fin.cons argument (Fin.cons function (Fin.cons remaining Fin.elim0)))))) psi
  intro β j ys Delta hj hq
  simp only [consTermRename,emptyRename] at hq
  have hs' := renameInto hs j Delta hj
  rw [InternalApplicationResultStackReturnFinishSupportProof.graph6Rename] at hs'
  let xs : Fin 6 → OTerm β := Fin.cons (d.relabel j) (Fin.cons (e.relabel j) (Fin.cons (tail.relabel j)
    (Fin.cons (argument.relabel j) (Fin.cons (function.relabel j) (Fin.cons (remaining.relabel j) Fin.elim0)))))
  have hv := binaryRecover InternalPairing.pairing (.projection 0) (.projection 1)
    (ys 0) (d.relabel j) (e.relabel j) xs (hq 0) (projectionValue 0 xs) (projectionValue 1 xs)
  have hf := binaryRecover InternalPairing.pairing (InternalLessThan.constantOne 6) _
    (ys 1) (suc z) (ys 0) xs (hq 1) (InternalLessThanSupportProof.oneConstantValue xs) (hq 0)
  have hw := binaryRecover InternalListCodec.consCode _ (.projection 2)
    (ys 2) (ys 1) (tail.relabel j) xs (hq 2) (hq 1) (projectionValue 2 xs)
  have ht := binaryRecover InternalListCodec.consCode (.projection 4) (.projection 5)
    (ys 3) (function.relabel j) (remaining.relabel j) xs (hq 3) (projectionValue 4 xs) (projectionValue 5 xs)
  have hr := binaryRecover InternalListCodec.consCode (.projection 3) _
    (ys 4) (argument.relabel j) (ys 3) xs (hq 4) (projectionValue 3 xs) (hq 3)
  have hi := binaryRecover InternalPairing.pairing _ _ (ys 5) (ys 2) (ys 4) xs (hq 5) (hq 2) (hq 4)
  have ho := binaryRecover InternalPairing.pairing (InternalLessThan.constantOne 6) _
    (state.relabel j) (suc z) (ys 5) xs hs' (InternalLessThanSupportProof.oneConstantValue xs) (hq 5)
  exact k β j Delta (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) hj
    (liveStateValue (state.relabel j) (ys 5) (ys 2) (ys 4) hi ho) hw hf hv hr ht

open InternalParameterizedApplicationResultStack

theorem liveInner (guard leaf : Program 2) (combine : Program 5)
    (state stack results frame tail out parameter : OTerm α)
    (hs : Nonempty (Derivation body Gamma (graph2 liveState state stack results)))
    (hc : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode stack frame tail)))
    (hi : Nonempty (Derivation body Gamma (graph2
      (InternalAcceptance.branch
        (liftP (InternalApplicationStepPeel.same frameTag (InternalAcceptance.constantZero 1)))
        (InternalAcceptance.branch (liftP (InternalApplicationValidityStack.exactOne frameTag))
          (InternalAcceptance.constantZero 2)
          (InternalAcceptance.branch (liftP InternalApplicationResultStack.results) (InternalAcceptance.constantZero 2)
            (InternalAcceptance.branch (liftP (tailOf InternalApplicationResultStack.results))
              (InternalAcceptance.constantZero 2) (finishReturnedP combine))))
        (InternalAcceptance.branch (wireP (openGuardP guard) ![currentValue])
          (leafReturnedP leaf) (liftP expanded))) out state parameter))) :
    Nonempty (Derivation body Gamma (graph2 (transitionP guard leaf combine) out state parameter)) := by
  let xs : Fin 2 → OTerm α := Fin.cons state (Fin.cons parameter Fin.elim0)
  let ss : Fin 1 → OTerm α := Fin.cons state Fin.elim0
  have hd := InternalListCodecSupportProof.consDestruction stack frame tail hc
  apply successorBranchIntro _ _ _ out z xs
    (liftValue _ (suc z) state parameter
      (sameAccept status (InternalLessThan.constantOne 1) (suc z) ss
        (liveStatus state stack results hs) (InternalLessThanSupportProof.oneConstantValue ss)))
  exact nonzeroBranchIntro _ _ _ out stack xs
    (liftValue _ stack state parameter (andLeft (liveStateFields state stack results hs)))
    (by simpa only [equalEqn] using andRight (andRight hd)) hi

theorem leafAt (guard leaf : Program 2) (combine : Program 5)
    (state stack results frame value tail out parameter leafValue : OTerm α)
    (hs : Nonempty (Derivation body Gamma (graph2 liveState state stack results)))
    (hc : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode stack frame tail)))
    (hp : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing frame z value)))
    (hg : Nonempty (Derivation body Gamma (graph2 (openGuardP guard) z value parameter)))
    (hl : Nonempty (Derivation body Gamma (graph2 leaf leafValue value parameter)))
    (hr : Nonempty (Derivation body Gamma (graph3 returnState out leafValue tail results))) :
    Nonempty (Derivation body Gamma (graph2 (transitionP guard leaf combine) out state parameter)) := by
  let xs : Fin 2 → OTerm α := Fin.cons state (Fin.cons parameter Fin.elim0)
  let ss : Fin 1 → OTerm α := Fin.cons state Fin.elim0
  have hf := currentFields state stack results frame tail z value hs hc hp
  have hrest := andLeft (andRight hf)
  have htag := andLeft (andRight (andRight hf))
  have hval := andRight (andRight (andRight hf))
  have hres := andRight (liveStateFields state stack results hs)
  have hl' := wireValue leaf ![currentValue] leafValue state parameter (Fin.cons value Fin.elim0)
    (by simpa only [appendParameterOne] using hl)
    (fun i => Fin.cases hval (fun k => Fin.elim0 k) i)
  have hg' := wireValue (openGuardP guard) ![currentValue] z state parameter (Fin.cons value Fin.elim0)
    (by simpa only [appendParameterOne] using hg)
    (fun i => Fin.cases hval (fun k => Fin.elim0 k) i)
  have hr' : Nonempty (Derivation body Gamma (graph2 (leafReturnedP leaf) out state parameter)) := by
    apply compositionValue returnState _ out xs (Fin.cons leafValue (Fin.cons tail (Fin.cons results Fin.elim0))) hr
    intro i
    exact Fin.cases hl' (Fin.cases (liftValue _ tail state parameter hrest)
      (Fin.cases (liftValue _ results state parameter hres) (fun k => Fin.elim0 k))) i
  apply liveInner guard leaf combine state stack results frame tail out parameter hs hc
  apply successorBranchIntro _ _ _ out z xs
    (liftValue _ (suc z) state parameter
      (sameAccept frameTag (InternalAcceptance.constantZero 1) z ss htag
        (InternalLessThanSupportProof.zeroConstantValue ss)))
  exact zeroBranchIntro _ _ _ out xs hg' hr'

theorem finishAt (guard leaf : Program 2) (combine : Program 5)
    (state stack results frame value d e tail argument function remaining afterArgument out parameter combinedValue : OTerm α)
    (hs : Nonempty (Derivation body Gamma (graph2 liveState state stack results)))
    (hc : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode stack frame tail)))
    (hp : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing frame (suc z) value)))
    (hv : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing value d e)))
    (hr : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode results argument afterArgument)))
    (ht : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode afterArgument function remaining)))
    (hcomb : Nonempty (Derivation body Gamma
      (programGraph combine combinedValue (Fin.cons d (Fin.cons e (Fin.cons function (Fin.cons argument (Fin.cons parameter Fin.elim0))))))))
    (hret : Nonempty (Derivation body Gamma (graph3 returnState out combinedValue tail remaining))) :
    Nonempty (Derivation body Gamma (graph2 (transitionP guard leaf combine) out state parameter)) := by
  let xs : Fin 2 → OTerm α := Fin.cons state (Fin.cons parameter Fin.elim0)
  let ss : Fin 1 → OTerm α := Fin.cons state Fin.elim0
  have hf := currentFields state stack results frame tail (suc z) value hs hc hp
  have hrest := andLeft (andRight hf)
  have htag := andLeft (andRight (andRight hf))
  have hval := andRight (andRight (andRight hf))
  have hres := andRight (liveStateFields state stack results hs)
  have hdom := unaryValue InternalUnpair.left currentValue d value ss (pairLeft value d e hv) hval
  have hcod := unaryValue InternalUnpair.right currentValue e value ss (pairRight value d e hv) hval
  have hdr := InternalListCodecSupportProof.consDestruction results argument afterArgument hr
  have hdt := InternalListCodecSupportProof.consDestruction afterArgument function remaining ht
  have harg := unaryValue InternalListCodec.headCode InternalApplicationResultStack.results
    argument results ss (andLeft hdr) hres
  have htail := unaryValue InternalListCodec.tailCode InternalApplicationResultStack.results
    afterArgument results ss (andLeft (andRight hdr)) hres
  have hfun := unaryValue InternalListCodec.headCode (tailOf InternalApplicationResultStack.results)
    function afterArgument ss (andLeft hdt) htail
  have hremaining := unaryValue InternalListCodec.tailCode (tailOf InternalApplicationResultStack.results)
    remaining afterArgument ss (andLeft (andRight hdt)) htail
  have hcomb' : Nonempty (Derivation body Gamma (graph2 (combinedP combine) combinedValue state parameter)) := by
    apply wireValue combine _ combinedValue state parameter (Fin.cons d (Fin.cons e (Fin.cons function (Fin.cons argument Fin.elim0))))
      (by simpa only [appendParameterFour] using hcomb)
    intro i
    exact Fin.cases hdom (Fin.cases hcod (Fin.cases hfun (Fin.cases harg (fun k => Fin.elim0 k)))) i
  have hret' : Nonempty (Derivation body Gamma (graph2 (finishReturnedP combine) out state parameter)) := by
    apply compositionValue returnState _ out xs (Fin.cons combinedValue (Fin.cons tail (Fin.cons remaining Fin.elim0))) hret
    intro i
    exact Fin.cases hcomb' (Fin.cases (liftValue _ tail state parameter hrest)
      (Fin.cases (liftValue _ remaining state parameter hremaining) (fun k => Fin.elim0 k))) i
  have htagNotZero := binaryValue InternalEqualityTest.equalityTest frameTag (InternalAcceptance.constantZero 1)
    z (suc z) z ss
    (InternalEqualityTestCompositionProof.rejectBackwardGap (suc z) z z ⟨InternalAdditionLawsProof.leftZero (suc z)⟩)
    htag (InternalLessThanSupportProof.zeroConstantValue ss)
  apply liveInner guard leaf combine state stack results frame tail out parameter hs hc
  apply zeroBranchIntro _ _ _ out xs (liftValue _ z state parameter htagNotZero)
  apply successorBranchIntro _ _ _ out z xs
    (liftValue _ (suc z) state parameter
      (sameAccept frameTag (InternalLessThan.constantOne 1) (suc z) ss htag
        (InternalLessThanSupportProof.oneConstantValue ss)))
  apply nonzeroBranchIntro _ _ _ out results xs (liftValue _ results state parameter hres)
    (by simpa only [equalEqn] using andRight (andRight hdr))
  exact nonzeroBranchIntro _ _ _ out afterArgument xs (liftValue _ afterArgument state parameter htail)
    (by simpa only [equalEqn] using andRight (andRight hdt)) hret'

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultStackReturnSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultStackReturnSupportProof
