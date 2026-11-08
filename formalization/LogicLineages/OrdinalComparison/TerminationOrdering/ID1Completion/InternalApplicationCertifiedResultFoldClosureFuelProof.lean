module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertifiedResultFoldClosureTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityClosureApplicationQueryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackCompositionBasicProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertifiedResultFoldClosureFuelProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertifiedResultFoldClosure InternalApplicationCertificateConstructors
open InternalPairingSumBounds InternalPairingSumBoundsProof InternalPairingSumBoundsArithmeticProof
open InternalApplicationResultStackComposition InternalApplicationResultStackCompositionSyntaxProof
open InternalApplicationResultStackCompositionRunProof InternalApplicationResultStackCompositionBasicProof
open InternalControlGraphSupportProof InternalUnpairReverseSyntaxProof
open InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open InternalAdditionLawsProof InternalAdditionCancellationProof InternalOriginalOrderSyntaxProof
open InternalUnpairReverseBoundsArithmeticProof InternalSourceInversionSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem runAtBound (guard leaf : Program 1) (combine : Program 4)
    (count fuel work initialResults finalResults : OTerm α)
    (hb : Nonempty (Derivation body Gamma (weakBound count fuel)))
    (hr : Nonempty (Derivation body Gamma (actualRun guard leaf combine count work initialResults finalResults))) :
    Nonempty (Derivation body Gamma (actualRun guard leaf combine fuel work initialResults finalResults)) := by
  apply weakOrderCases Gamma count fuel _ hb
  intro β j Delta padding hj he
  rw [actualRunRename]
  have hr' := renameInto hr j Delta hj
  rw [actualRunRename] at hr'
  exact countTransport guard leaf combine (add (count.relabel j) padding) (fuel.relabel j)
    (work.relabel j) (initialResults.relabel j) (finalResults.relabel j) he
    (runPadding guard leaf combine (count.relabel j) padding (work.relabel j)
      (initialResults.relabel j) (finalResults.relabel j) hr')

def interchange (a b c d : OTerm α) :
    Derivation body Gamma (eqn (add (add a b) (add c d)) (add (add a c) (add b d))) := by
  exact trans (associativity a b (add c d))
    (trans (congAddLeft a (symm (associativity b c d)))
      (trans (congAddLeft a (InternalMultiplicationLawsProof.congAddRight d (commutativity b c)))
        (trans (congAddLeft a (associativity c b d))
          (symm (associativity a c (add b d))))))

def fuelCountExpansion (fp ap : OTerm α) :
    Derivation body Gamma (eqn
      (suc (add (payloadFuel fp) (add (payloadFuel ap) (suc z))))
      (add (childFuelSum fp ap) (childFuelSum fp ap))) := by
  let f := add fp fp
  let a := add ap ap
  have ha : Derivation body Gamma (eqn (add (suc a) (suc z)) (suc (suc a))) :=
    trans (leftSuccessor a (suc z)) (congSuc (trans (addSucc a z) (congSuc (addZero a))))
  have hs : Derivation body Gamma (eqn
      (suc (add (suc f) (add (suc a) (suc z)))) (suc (suc (suc (suc (add f a)))))) :=
    congSuc (trans (congAddLeft (suc f) ha)
      (trans (leftSuccessor f (suc (suc a)))
        (congSuc (trans (addSucc f (suc a)) (congSuc (addSucc f a))))))
  have hc : Derivation body Gamma (eqn (childFuelSum fp ap) (suc (suc (add fp ap)))) :=
    trans (leftSuccessor fp (suc ap)) (congSuc (addSucc fp ap))
  have hd : Derivation body Gamma (eqn (add (childFuelSum fp ap) (childFuelSum fp ap))
      (suc (suc (suc (suc (add (add fp ap) (add fp ap))))))) := by
    let x := add fp ap
    exact trans (InternalMultiplicationLawsProof.congAddRight (childFuelSum fp ap) hc)
      (trans (congAddLeft (suc (suc x)) hc)
        (trans (leftSuccessor (suc x) (suc (suc x)))
          (congSuc (trans (leftSuccessor x (suc (suc x)))
            (congSuc (trans (addSucc x (suc x)) (congSuc (addSucc x x))))))))
  exact trans hs (trans (congSuc (congSuc (congSuc (congSuc (interchange fp fp ap ap))))) (symm hd))

theorem fuelBoundAtWitnesses (payload middle children d fp ap : OTerm α)
    (h : Nonempty (Derivation body Gamma (applicationPayloadWitnesses payload middle children d fp ap))) :
    Nonempty (Derivation body Gamma (weakBound
      (suc (add (payloadFuel fp) (add (payloadFuel ap) (suc z)))) (payloadFuel payload))) := by
  have hc := InternalRecursionClosureLogicProof.closedApply
    (actualOriginalApplicationPayloadChildFuelBound body α payload middle children d fp ap) h
  let c := childFuelSum fp ap
  have h1 := addWeakRight c payload c hc
  have h2 := addWeakLeft payload c payload hc
  have h3 := weakTrans (add c c) (add payload c) (add payload payload) h1 h2
  obtain ⟨hp⟩ := rightWeakAdd (body := body) (Gamma := Gamma) (suc z) (add payload payload)
  have hep : Derivation body Gamma (eqn (add (suc z) (add payload payload)) (suc (add payload payload))) :=
    trans (leftSuccessor z (add payload payload)) (congSuc (leftZero (add payload payload)))
  have hnext : Nonempty (Derivation body Gamma (weakBound (add payload payload) (suc (add payload payload)))) :=
    ⟨InternalSquareRootArithmeticSupportProof.orderRight (add payload payload) (congSuc hep) hp⟩
  have h4 := weakTrans (add c c) (add payload payload) (suc (add payload payload)) h3 hnext
  obtain ⟨h4⟩ := h4
  exact ⟨InternalSquareRootArithmeticSupportProof.orderLeft (suc (payloadFuel payload)) (symm (fuelCountExpansion fp ap)) h4⟩

open InternalApplicationValidityClosureApplicationQueryProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof InternalApplicationStepPeelComponentsProof
open InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof

theorem applicationFuelBound (arrow d e fp ap fn arg parent payload : OTerm α)
    (hparent : Nonempty (Derivation body Gamma (graph4 packedApplication parent d e fp ap)))
    (hright : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right payload parent))) :
    Nonempty (Derivation body Gamma (weakBound
      (suc (add (payloadFuel fp) (add (payloadFuel ap) (suc z)))) (payloadFuel payload))) := by
  apply queryCases queries
    (Fin.cons d (Fin.cons e (Fin.cons fp (Fin.cons ap (Fin.cons arrow
      (Fin.cons fn (Fin.cons arg (Fin.cons parent Fin.elim0)))))))) _
  intro β j ys Delta hj hq
  change Nonempty (Derivation body Delta ((ltF
    (suc (add (payloadFuel fp) (add (payloadFuel ap) (suc z))))
    (suc (payloadFuel payload))).relabel j))
  simp only [orderRename, payloadFuel, sucRelabel, addRelabel, zRelabel]
  have hparent' := renameInto hparent j Delta hj
  have hright' := renameInto hright j Delta hj
  simp only [graph1Rename, graph4Rename] at hparent' hright'
  simp only [consTermRename,emptyRename] at hq
  let xs : Fin 8 → OTerm β :=
    Fin.cons (d.relabel j) (Fin.cons (e.relabel j) (Fin.cons (fp.relabel j)
      (Fin.cons (ap.relabel j) (Fin.cons (arrow.relabel j) (Fin.cons (fn.relabel j)
        (Fin.cons (arg.relabel j) (Fin.cons (parent.relabel j) Fin.elim0)))))))
  have hc := binaryRecover InternalPairing.pairing (.projection 2) (.projection 3)
    (ys 0) (fp.relabel j) (ap.relabel j) xs (hq 0) (projectionValue 2 xs) (projectionValue 3 xs)
  have hm := binaryRecover InternalPairing.pairing (.projection 0) childrenQ
    (ys 1) (d.relabel j) (ys 0) xs (hq 1) (projectionValue 0 xs) (hq 0)
  have hp := binaryRecover InternalPairing.pairing (two 8) middleQ
    (ys 2) (suc (suc z)) (ys 1) xs (hq 2) (twoValue xs) (hq 1)
  have hpp := binaryRecover InternalPairing.pairing (.projection 1) payloadQ
    (ys 3) (e.relabel j) (ys 2) xs (hq 3) (projectionValue 1 xs) (hq 2)
  have hpacked := packedAtPairs (d.relabel j) (e.relabel j) (fp.relabel j) (ap.relabel j)
    (ys 0) (ys 1) (ys 2) (ys 3) hc hm hp hpp
  have he := valueUnique packedApplication (ys 3) (parent.relabel j)
    (Fin.cons (d.relabel j) (Fin.cons (e.relabel j)
      (Fin.cons (fp.relabel j) (Fin.cons (ap.relabel j) Fin.elim0)))) hpacked hparent'
  have hparentPair := outputTransport InternalPairing.pairing (ys 3) (parent.relabel j)
    (Fin.cons (e.relabel j) (Fin.cons (ys 2) Fin.elim0)) he hpp
  have hpr := pairRight (parent.relabel j) (e.relabel j) (ys 2) hparentPair
  have heq := valueUnique InternalUnpair.right (ys 2) (payload.relabel j)
    (Fin.cons (parent.relabel j) Fin.elim0) hpr hright'
  have hp' := outputTransport InternalPairing.pairing (ys 2) (payload.relabel j)
    (Fin.cons (suc (suc z)) (Fin.cons (ys 1) Fin.elim0)) heq hp
  exact fuelBoundAtWitnesses (payload.relabel j) (ys 1) (ys 0) (d.relabel j)
    (fp.relabel j) (ap.relabel j) (andIntro hp' (andIntro hm hc))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertifiedResultFoldClosureFuelProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertifiedResultFoldClosureFuelProof
