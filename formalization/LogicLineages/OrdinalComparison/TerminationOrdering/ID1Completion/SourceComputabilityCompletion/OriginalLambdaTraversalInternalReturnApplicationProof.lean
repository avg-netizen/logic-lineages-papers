module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackReturnFinishSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalTargets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalReturnApplicationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationResultStack
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalAcceptanceBranchProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open InternalTagArithmeticSupportProof InternalGraphCompositionFunctionalityProof
open InternalApplicationResultStackReturnSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}
open InternalApplicationResultStackReturnFinishSupportProof
theorem transitionFromQueries (leaf : Program 2)
    (d e work argument function results state : OTerm α) (ys : Fin 10 → OTerm α)
    (hs : Nonempty (Derivation body Gamma (programGraph OriginalLambdaTraversalInternal.applicationReturnState state ![d,e,work,argument,function,results])))
    (hq : ∀ i, Nonempty (Derivation body Gamma (programGraph (queries application i) (ys i)
      (Fin.cons d (Fin.cons e (Fin.cons work (Fin.cons argument (Fin.cons function (Fin.cons results Fin.elim0))))))))) :
    Nonempty (Derivation body Gamma (graph1 (OriginalLambdaTraversal.transition leaf) (ys 9) state)) := by
  let xs : Fin 6 → OTerm α := Fin.cons d (Fin.cons e (Fin.cons work
    (Fin.cons argument (Fin.cons function (Fin.cons results Fin.elim0)))))
  let ss : Fin 1 → OTerm α := Fin.cons state Fin.elim0
  have ht := binaryRecover InternalPairing.pairing (.projection 0) (.projection 1)
    (ys 0) d e xs (hq 0) (projectionValue 0 xs) (projectionValue 1 xs)
  have hf := binaryRecover InternalPairing.pairing (InternalLessThan.constantOne 6) typeQ
    (ys 1) (suc z) (ys 0) xs (hq 1) (InternalLessThanSupportProof.oneConstantValue xs) (hq 0)
  have hw := binaryRecover InternalListCodec.consCode frameQ (.projection 2)
    (ys 2) (ys 1) work xs (hq 2) (hq 1) (projectionValue 2 xs)
  have hrt := binaryRecover InternalListCodec.consCode (.projection 4) (.projection 5)
    (ys 3) function results xs (hq 3) (projectionValue 4 xs) (projectionValue 5 xs)
  have hr := binaryRecover InternalListCodec.consCode (.projection 3) tailResultsQ
    (ys 4) argument (ys 3) xs (hq 4) (projectionValue 3 xs) (hq 3)
  have hi := binaryRecover InternalPairing.pairing workQ resultsQ
    (ys 5) (ys 2) (ys 4) xs (hq 5) (hq 2) (hq 4)
  have ho := binaryRecover InternalPairing.pairing (InternalLessThan.constantOne 6) oldPairQ
    state (suc z) (ys 5) xs hs (InternalLessThanSupportProof.oneConstantValue xs) (hq 5)
  have hstatus := pairLeft state (suc z) (ys 5) ho
  have hinner := pairRight state (suc z) (ys 5) ho
  have hwork := unaryValue InternalUnpair.left InternalUnpair.right (ys 2) (ys 5) ss
    (pairLeft (ys 5) (ys 2) (ys 4) hi) hinner
  have hresults := unaryValue InternalUnpair.right InternalUnpair.right (ys 4) (ys 5) ss
    (pairRight (ys 5) (ys 2) (ys 4) hi) hinner
  have hdw := InternalListCodecSupportProof.consDestruction (ys 2) (ys 1) work hw
  have hframe := unaryValue InternalListCodec.headCode InternalApplicationResultStack.work
    (ys 1) (ys 2) ss (andLeft hdw) hwork
  have hrest := unaryValue InternalListCodec.tailCode InternalApplicationResultStack.work
    work (ys 2) ss (andLeft (andRight hdw)) hwork
  have htag := unaryValue InternalUnpair.left currentFrame (suc z) (ys 1) ss
    (pairLeft (ys 1) (suc z) (ys 0) hf) hframe
  have hvalue := unaryValue InternalUnpair.right currentFrame (ys 0) (ys 1) ss
    (pairRight (ys 1) (suc z) (ys 0) hf) hframe
  have hdom := unaryValue InternalUnpair.left currentValue d (ys 0) ss (pairLeft (ys 0) d e ht) hvalue
  have hcod := unaryValue InternalUnpair.right currentValue e (ys 0) ss (pairRight (ys 0) d e ht) hvalue
  have hdr := InternalListCodecSupportProof.consDestruction (ys 4) argument (ys 3) hr
  have hdt := InternalListCodecSupportProof.consDestruction (ys 3) function results hrt
  have harg := unaryValue InternalListCodec.headCode InternalApplicationResultStack.results
    argument (ys 4) ss (andLeft hdr) hresults
  have htail := unaryValue InternalListCodec.tailCode InternalApplicationResultStack.results
    (ys 3) (ys 4) ss (andLeft (andRight hdr)) hresults
  have hfun := unaryValue InternalListCodec.headCode (tailOf InternalApplicationResultStack.results)
    function (ys 3) ss (andLeft hdt) htail
  have hremaining := unaryValue InternalListCodec.tailCode (tailOf InternalApplicationResultStack.results)
    results (ys 3) ss (andLeft (andRight hdt)) htail
  have hc : Nonempty (Derivation body Gamma (graph1 (combined application) (ys 6) state)) := by
    apply compositionValue application _ (ys 6) ss
      (Fin.cons d (Fin.cons e (Fin.cons function (Fin.cons argument Fin.elim0))))
      ((returnFromQueries application d e work argument function results ys hq).1)
    intro i
    exact Fin.cases hdom (Fin.cases hcod (Fin.cases hfun (Fin.cases harg (fun k => Fin.elim0 k)))) i
  have hnr := binaryRecover InternalListCodec.consCode (combineQ application) (.projection 5)
    (ys 7) (ys 6) results xs (hq 7) (hq 6) (projectionValue 5 xs)
  have hnp := binaryRecover InternalPairing.pairing (.projection 2) (newResultsQ application)
    (ys 8) work (ys 7) xs (hq 8) (projectionValue 2 xs) (hq 7)
  have hns := binaryRecover InternalPairing.pairing (InternalLessThan.constantOne 6) (newPairQ application)
    (ys 9) (suc z) (ys 8) xs (hq 9) (InternalLessThanSupportProof.oneConstantValue xs) (hq 8)
  have hrl := binaryValue InternalListCodec.consCode (combined application)
    (tailOf (tailOf InternalApplicationResultStack.results)) (ys 7) (ys 6) results ss hnr hc hremaining
  have hnewpair := binaryValue InternalPairing.pairing rest
    (consOf (combined application) (tailOf (tailOf InternalApplicationResultStack.results)))
    (ys 8) work (ys 7) ss hnp hrest hrl
  have hreturned : Nonempty (Derivation body Gamma (graph1 (finishReturned application) (ys 9) state)) :=
    binaryValue InternalPairing.pairing _ _ (ys 9) (suc z) (ys 8) ss hns
      (InternalLessThanSupportProof.oneConstantValue ss) hnewpair
  have hstatusOne := sameAccept status (InternalLessThan.constantOne 1) (suc z) ss hstatus
    (InternalLessThanSupportProof.oneConstantValue ss)
  have htagOne := sameAccept frameTag (InternalLessThan.constantOne 1) (suc z) ss htag
    (InternalLessThanSupportProof.oneConstantValue ss)
  have htagNotZero := binaryValue InternalEqualityTest.equalityTest frameTag (InternalAcceptance.constantZero 1)
    z (suc z) z ss
    (InternalEqualityTestCompositionProof.rejectBackwardGap (suc z) z z ⟨InternalAdditionLawsProof.leftZero (suc z)⟩)
    htag (InternalLessThanSupportProof.zeroConstantValue ss)
  apply successorBranchIntro _ _ _ (ys 9) z ss hstatusOne
  apply nonzeroBranchIntro _ _ _ (ys 9) (ys 2) ss hwork (by simpa only [equalEqn] using (andRight (andRight hdw)))
  apply zeroBranchIntro _ _ _ (ys 9) ss htagNotZero
  apply successorBranchIntro _ _ _ (ys 9) z ss htagOne
  apply nonzeroBranchIntro _ _ _ (ys 9) (ys 4) ss hresults (by simpa only [equalEqn] using (andRight (andRight hdr)))
  exact nonzeroBranchIntro _ _ _ (ys 9) (ys 3) ss htail (by simpa only [equalEqn] using (andRight (andRight hdt))) hreturned
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalReturnApplicationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalReturnApplicationProof
