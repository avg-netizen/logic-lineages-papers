module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackInternalSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPairingSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendTransitionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationValidityStack
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof InternalApplicationStepPeelComponentsProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalAcceptanceBranchProof
open InternalAcceptanceConjunctionProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof InternalGraphCompositionFunctionalityProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- No numeric execution is used: the original pair graph supplies both selectors. -/
theorem terminalFromPair (node leaf : Program 1) (state : OTerm α)
    (hp : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing state (suc z) z))) :
    Nonempty (Derivation body Gamma (graph1 (transition node leaf) state state)) := by
  let xs : Fin 1 → OTerm α := Fin.cons state Fin.elim0
  apply successorBranchIntro _ _ _ state z xs
    (sameAccept status (InternalLessThan.constantOne 1) (suc z) xs
      (pairLeft state (suc z) z hp) (InternalLessThanSupportProof.oneConstantValue xs))
  exact zeroBranchIntro work _ _ state xs (pairRight state (suc z) z hp) (projectionValue 0 xs)

/-- The live state exposes its literal list head, tail, and nonzero work code. -/
theorem liveConsFields (state stack head tail : OTerm α)
    (hp : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing state (suc z) stack)))
    (hc : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode stack head tail))) :
    Nonempty (Derivation body Gamma
      (graph1 current head state ⊓ (graph1 rest tail state ⊓ (eqn stack z).not))) := by
  let xs : Fin 1 → OTerm α := Fin.cons state Fin.elim0
  have hd := InternalListCodecSupportProof.consDestruction stack head tail hc
  have hw := pairRight state (suc z) stack hp
  exact andIntro
    (unaryValue InternalListCodec.headCode work head stack xs (andLeft hd) hw)
    (andIntro (unaryValue InternalListCodec.tailCode work tail stack xs (andLeft (andRight hd)) hw)
      (andRight (andRight hd)))

/-- Transport shared raw-head unpair queries to the two selectors used by the guard. -/
theorem headFields (state head ty payload tag : OTerm α)
    (hh : Nonempty (Derivation body Gamma (graph1 current head state)))
    (ht : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left ty head)))
    (hp : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right payload head)))
    (hg : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left tag payload))) :
    Nonempty (Derivation body Gamma (graph1 currentType ty state ⊓ graph1 currentTag tag state)) := by
  let xs : Fin 1 → OTerm α := Fin.cons state Fin.elim0
  exact andIntro (unaryValue InternalUnpair.left current ty head xs ht hh)
    (unaryValue InternalUnpair.left (rightOf current) tag payload xs hg
      (unaryValue InternalUnpair.right current payload head xs hp hh))

/-- Shared actual equality-test outputs become the literal current-tag control. -/
theorem tagControl (state tag test : OTerm α)
    (ht : Nonempty (Derivation body Gamma (graph1 currentTag tag state)))
    (he : Nonempty (Derivation body Gamma (graph2 InternalEqualityTest.equalityTest test tag positionTerm))) :
    Nonempty (Derivation body Gamma
      (graph1 (InternalApplicationStepPeel.same currentTag (two 1)) test state)) :=
  binaryValue InternalEqualityTest.equalityTest currentTag (two 1) test tag positionTerm
    (Fin.cons state Fin.elim0) he ht (twoValue _)

/-- Shared actual guard outputs and equality-test outputs, with no semantic guard premise. -/
theorem guardControl (p selector : Program 1) (state input value test : OTerm α)
    (hs : Nonempty (Derivation body Gamma (graph1 selector input state)))
    (hp : Nonempty (Derivation body Gamma (graph1 p value input)))
    (he : Nonempty (Derivation body Gamma (graph2 InternalEqualityTest.equalityTest test value (suc z)))) :
    Nonempty (Derivation body Gamma
      (graph1 (exactOne (.composition p (fun _ : Fin 1 => selector))) test state)) :=
  binaryValue InternalEqualityTest.equalityTest _ _ test value (suc z) (Fin.cons state Fin.elim0)
    he (unaryValue p selector value input (Fin.cons state Fin.elim0) hp hs)
    (InternalLessThanSupportProof.oneConstantValue _)

/-- Discharge the common status/work envelope around either head branch. -/
theorem liveConsInner (node leaf : Program 1) (state stack head tail out : OTerm α)
    (hp : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing state (suc z) stack)))
    (hc : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode stack head tail)))
    (hi : Nonempty (Derivation body Gamma (graph1
      (InternalAcceptance.branch (InternalApplicationStepPeel.same currentTag (two 1))
        (InternalAcceptance.branch (exactOne (.composition leaf (fun _ : Fin 1 => current)))
          (InternalAcceptance.constantZero 1) popped)
        (InternalAcceptance.branch (exactOne (.composition node (fun _ : Fin 1 => currentType)))
          (InternalAcceptance.constantZero 1) expanded)) out state))) :
    Nonempty (Derivation body Gamma (graph1 (transition node leaf) out state)) := by
  let xs : Fin 1 → OTerm α := Fin.cons state Fin.elim0
  have hd := liveConsFields state stack head tail hp hc
  apply successorBranchIntro _ _ _ out z xs
    (sameAccept status (InternalLessThan.constantOne 1) (suc z) xs
      (pairLeft state (suc z) stack hp) (InternalLessThanSupportProof.oneConstantValue xs))
  exact branchValue work (.projection 0) _ out stack state out xs
    (pairRight state (suc z) stack hp) (projectionValue 0 xs) hi
    (InternalControlGraphProof.conditionalAtNonzero stack state out (andRight (andRight hd)))

theorem leafPop (node leaf : Program 1) (state stack head tail out : OTerm α)
    (hp : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing state (suc z) stack)))
    (hc : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode stack head tail)))
    (ht : Nonempty (Derivation body Gamma (graph1 (InternalApplicationStepPeel.same currentTag (two 1)) z state)))
    (hl : Nonempty (Derivation body Gamma
      (graph1 (exactOne (.composition leaf (fun _ : Fin 1 => current))) (suc z) state)))
    (ho : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing out (suc z) tail))) :
    Nonempty (Derivation body Gamma (graph1 (transition node leaf) out state)) := by
  let xs : Fin 1 → OTerm α := Fin.cons state Fin.elim0
  apply liveConsInner node leaf state stack head tail out hp hc
  apply zeroBranchIntro _ _ _ out xs ht
  apply successorBranchIntro _ _ _ out z xs hl
  exact binaryValue InternalPairing.pairing _ _ out (suc z) tail xs ho
    (InternalLessThanSupportProof.oneConstantValue xs)
    (andLeft (andRight (liveConsFields state stack head tail hp hc)))

theorem leafReject (node leaf : Program 1) (state stack head tail : OTerm α)
    (hp : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing state (suc z) stack)))
    (hc : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode stack head tail)))
    (ht : Nonempty (Derivation body Gamma (graph1 (InternalApplicationStepPeel.same currentTag (two 1)) z state)))
    (hl : Nonempty (Derivation body Gamma
      (graph1 (exactOne (.composition leaf (fun _ : Fin 1 => current))) z state))) :
    Nonempty (Derivation body Gamma (graph1 (transition node leaf) z state)) := by
  apply liveConsInner node leaf state stack head tail z hp hc
  apply zeroBranchIntro _ _ _ z (Fin.cons state Fin.elim0) ht
  exact zeroBranchIntro _ _ _ z (Fin.cons state Fin.elim0) hl (constantZeroValue _)

theorem nodeReject (node leaf : Program 1) (state stack head tail : OTerm α)
    (hp : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing state (suc z) stack)))
    (hc : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode stack head tail)))
    (ht : Nonempty (Derivation body Gamma (graph1 (InternalApplicationStepPeel.same currentTag (two 1)) (suc z) state)))
    (hn : Nonempty (Derivation body Gamma
      (graph1 (exactOne (.composition node (fun _ : Fin 1 => currentType))) z state))) :
    Nonempty (Derivation body Gamma (graph1 (transition node leaf) z state)) := by
  apply liveConsInner node leaf state stack head tail z hp hc
  apply successorBranchIntro _ _ _ z z (Fin.cons state Fin.elim0) ht
  exact zeroBranchIntro _ _ _ z (Fin.cons state Fin.elim0) hn (constantZeroValue _)

/-- Arbitrary raw heads are supported; there is no packed-application decoder premise. -/
theorem nodeExpand (node leaf : Program 1) (state stack head tail fn arg suffix newWork out : OTerm α)
    (hp : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing state (suc z) stack)))
    (hc : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode stack head tail)))
    (ht : Nonempty (Derivation body Gamma (graph1 (InternalApplicationStepPeel.same currentTag (two 1)) (suc z) state)))
    (hn : Nonempty (Derivation body Gamma
      (graph1 (exactOne (.composition node (fun _ : Fin 1 => currentType))) (suc z) state)))
    (hf : Nonempty (Derivation body Gamma (graph1 currentFunction fn state)))
    (ha : Nonempty (Derivation body Gamma (graph1 currentArgument arg state)))
    (hs : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode suffix arg tail)))
    (hw : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode newWork fn suffix)))
    (ho : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing out (suc z) newWork))) :
    Nonempty (Derivation body Gamma (graph1 (transition node leaf) out state)) := by
  let xs : Fin 1 → OTerm α := Fin.cons state Fin.elim0
  apply liveConsInner node leaf state stack head tail out hp hc
  apply successorBranchIntro _ _ _ out z xs ht
  apply successorBranchIntro _ _ _ out z xs hn
  apply binaryValue InternalPairing.pairing _ _ out (suc z) newWork xs ho
    (InternalLessThanSupportProof.oneConstantValue xs)
  apply binaryValue InternalListCodec.consCode _ _ newWork fn suffix xs hw hf
  exact binaryValue InternalListCodec.consCode _ _ suffix arg tail xs hs ha
    (andLeft (andRight (liveConsFields state stack head tail hp hc)))

/-- Every child field is queried on the shared raw head, independently of its stack tail. -/
theorem headChildren (state head ty payload nodeBody children domain fp ap arrow fn arg : OTerm α)
    (hh : Nonempty (Derivation body Gamma (graph1 current head state)))
    (ht : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left ty head)))
    (hp : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right payload head)))
    (hb : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right nodeBody payload)))
    (hd : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left domain nodeBody)))
    (hc : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right children nodeBody)))
    (hf : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left fp children)))
    (ha : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right ap children)))
    (har : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode arrow domain ty)))
    (hfn : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing fn arrow fp)))
    (hag : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing arg domain ap))) :
    Nonempty (Derivation body Gamma (graph1 currentFunction fn state ⊓ graph1 currentArgument arg state)) := by
  let xs : Fin 1 → OTerm α := Fin.cons state Fin.elim0
  have hty : Nonempty (Derivation body Gamma (graph1 currentType ty state)) :=
    unaryValue InternalUnpair.left current ty head xs ht hh
  have hpay := unaryValue InternalUnpair.right current payload head xs hp hh
  have hbody := unaryValue InternalUnpair.right (rightOf current) nodeBody payload xs hb hpay
  have hdom : Nonempty (Derivation body Gamma (graph1 currentDomain domain state)) :=
    unaryValue InternalUnpair.left (InternalApplicationStepPeel.appBody current) domain nodeBody xs hd hbody
  have hch := unaryValue InternalUnpair.right (InternalApplicationStepPeel.appBody current)
    children nodeBody xs hc hbody
  have hfp := unaryValue InternalUnpair.left (rightOf (InternalApplicationStepPeel.appBody current))
    fp children xs hf hch
  have hap := unaryValue InternalUnpair.right (rightOf (InternalApplicationStepPeel.appBody current))
    ap children xs ha hch
  have hArrow := binaryValue InternalListCodec.consCode currentDomain currentType arrow domain ty xs har hdom hty
  exact andIntro (binaryValue InternalPairing.pairing _ _ fn arrow fp xs hfn hArrow hfp)
    (binaryValue InternalPairing.pairing _ _ arg domain ap xs hag hdom hap)

open InternalTagArithmeticSyntaxProof (zRelabel)
open InternalAdditionLawsProof InternalMultiplicationLawsProof

/-- The arithmetic ordering cannot put any number below zero. -/
theorem notLessZero (x : OTerm α) :
    Nonempty (Derivation body Gamma (InternalOriginalOrderSyntaxProof.ltF x z).not) := by
  have h : Nonempty (Derivation body
      (InternalOriginalOrderSyntaxProof.ltF x z :: Gamma) (⊥ : Formula α)) := by
    apply InternalOriginalOrderProof.orderCases _ x z _ ⟨Derivation.hypothesis List.mem_cons_self⟩
    intro β j Delta gap _ ⟨he⟩
    simp only [zRelabel] at he
    exact ⟨sucNeZeroApply (trans (symm (addSucc (x.relabel j) gap)) he)⟩
  obtain ⟨h⟩ := h
  exact ⟨Derivation.implicationIntroduction h⟩

theorem pairZero :
    Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing (z : OTerm α) z z)) := by
  have hp := InternalPairingSupportProof.pairingOfNotLess (body := body) (Gamma := Gamma) z z (notLessZero z)
  apply outputTransport InternalPairing.pairing (add (add (mul z z) z) z) z
    (Fin.cons z (Fin.cons z Fin.elim0)) _ hp
  exact ⟨trans (addZero (add (mul z z) z)) (trans (addZero (mul z z)) (mulZero z))⟩

theorem pairOneZero :
    Nonempty (Derivation body Gamma
      (graph2 InternalPairing.pairing (suc (suc (z : OTerm α))) (suc z) z)) := by
  have hp := InternalPairingSupportProof.pairingOfNotLess (body := body) (Gamma := Gamma)
    (suc z) z (notLessZero (suc z))
  have hm : Derivation body Gamma (eqn (mul (suc (z : OTerm α)) (suc z)) (suc z)) :=
    trans (mulSucc (suc z) z)
      (trans (InternalMultiplicationLawsProof.congAddRight (suc z) (mulZero (suc z)))
        (leftZero (suc z)))
  apply outputTransport InternalPairing.pairing (add (add (mul (suc z) (suc z)) (suc z)) z)
    (suc (suc z)) (Fin.cons (suc z) (Fin.cons z Fin.elim0)) _ hp
  exact ⟨trans (addZero _) (trans (addSucc _ z)
    (congSuc (trans (addZero _) hm)))⟩

theorem terminalFixed (node leaf : Program 1) :
    Nonempty (Derivation body Gamma
      (graph1 (transition node leaf) (suc (suc (z : OTerm α))) (suc (suc z)))) :=
  terminalFromPair node leaf _ pairOneZero

theorem failureFixed (node leaf : Program 1) :
    Nonempty (Derivation body Gamma (graph1 (transition node leaf) (z : OTerm α) z)) := by
  let xs : Fin 1 → OTerm α := Fin.cons z Fin.elim0
  have hs : Nonempty (Derivation body Gamma (graph1 status (z : OTerm α) z)) :=
    pairLeft z z z pairZero
  have he := InternalEqualityTestCompositionProof.rejectForwardGap (body := body) (Gamma := Gamma)
    (z : OTerm α) (suc z) z ⟨leftZero (suc z)⟩
  apply zeroBranchIntro _ _ _ z xs
  · exact binaryValue InternalEqualityTest.equalityTest status (InternalLessThan.constantOne 1)
      z z (suc z) xs he hs (InternalLessThanSupportProof.oneConstantValue xs)
  · exact constantZeroValue xs

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendTransitionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendTransitionProof
