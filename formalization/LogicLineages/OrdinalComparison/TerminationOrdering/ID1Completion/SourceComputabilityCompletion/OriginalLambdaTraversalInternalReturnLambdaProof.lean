module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackReturnFinishSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalTargets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalReturnLambdaProof
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
def typeQ : Program 5 := pairOf (.projection 0) (.projection 1)
def frameQ : Program 5 := OriginalLambdaTraversal.lambdaReturnOf (.projection 0) (.projection 1)
def workQ : Program 5 := consOf frameQ (.projection 2)
def resultsQ : Program 5 := consOf (.projection 3) (.projection 4)
def oldPairQ : Program 5 := pairOf workQ resultsQ
def constructorQ : Program 5 := .composition OriginalLambdaConstructor.constructor ![.projection 0,.projection 1,.projection 3]
def newResultsQ : Program 5 := consOf constructorQ (.projection 4)
def newPairQ : Program 5 := pairOf (.projection 2) newResultsQ
def newStateQ : Program 5 := liveOf (.projection 2) newResultsQ
def queries : Fin 9 → Program 5 := ![typeQ,frameQ,workQ,resultsQ,oldPairQ,constructorQ,newResultsQ,newPairQ,newStateQ]

theorem returnFromQueries
    (d e work value results : OTerm α) (ys : Fin 9 → OTerm α)
    (hq : ∀ i, Nonempty (Derivation body Gamma (programGraph (queries i) (ys i)
      ![d,e,work,value,results]))) :
    Nonempty (Derivation body Gamma (graph3 OriginalLambdaConstructor.constructor (ys 5) d e value)) ∧
    Nonempty (Derivation body Gamma (graph3 returnState (ys 8) (ys 5) work results)) := by
  let xs : Fin 5 → OTerm α := ![d,e,work,value,results]
  have hc : Nonempty (Derivation body Gamma (graph3 OriginalLambdaConstructor.constructor (ys 5) d e value)) := by
    apply compositionRecover OriginalLambdaConstructor.constructor ![.projection 0,.projection 1,.projection 3]
      (ys 5) xs ![d,e,value] (hq 5)
    intro i
    exact Fin.cases (projectionValue 0 xs) (Fin.cases (projectionValue 1 xs)
      (Fin.cases (projectionValue 3 xs) (fun k => Fin.elim0 k))) i
  have hr := binaryRecover InternalListCodec.consCode constructorQ (.projection 4)
    (ys 6) (ys 5) results xs (hq 6) (hq 5) (projectionValue 4 xs)
  have hi := binaryRecover InternalPairing.pairing (.projection 2) newResultsQ
    (ys 7) work (ys 6) xs (hq 7) (projectionValue 2 xs) (hq 6)
  have ho := binaryRecover InternalPairing.pairing (InternalLessThan.constantOne 5) newPairQ
    (ys 8) (suc z) (ys 7) xs (hq 8) (InternalLessThanSupportProof.oneConstantValue xs) (hq 7)
  let rs : Fin 3 → OTerm α := ![ys 5,work,results]
  have hr' := binaryValue InternalListCodec.consCode (.projection 0) (.projection 2)
    (ys 6) (ys 5) results rs hr (projectionValue 0 rs) (projectionValue 2 rs)
  have hi' := binaryValue InternalPairing.pairing (.projection 1) (consOf (.projection 0) (.projection 2))
    (ys 7) work (ys 6) rs hi (projectionValue 1 rs) hr'
  exact ⟨hc,binaryValue InternalPairing.pairing _ _ (ys 8) (suc z) (ys 7) rs ho
    (InternalLessThanSupportProof.oneConstantValue rs) hi'⟩

theorem transitionFromQueries (leaf : Program 2)
    (d e work value results state : OTerm α) (ys : Fin 9 → OTerm α)
    (hs : Nonempty (Derivation body Gamma (programGraph OriginalLambdaTraversalInternal.lambdaReturnState state ![d,e,work,value,results])))
    (hq : ∀ i, Nonempty (Derivation body Gamma (programGraph (queries i) (ys i)
      ![d,e,work,value,results]))) :
    Nonempty (Derivation body Gamma (graph1 (OriginalLambdaTraversal.transition leaf) (ys 8) state)) := by
  let xs : Fin 5 → OTerm α := ![d,e,work,value,results]
  let ss : Fin 1 → OTerm α := Fin.cons state Fin.elim0
  have ht := binaryRecover InternalPairing.pairing (.projection 0) (.projection 1)
    (ys 0) d e xs (hq 0) (projectionValue 0 xs) (projectionValue 1 xs)
  have hf := binaryRecover InternalPairing.pairing (two 5) typeQ
    (ys 1) (suc (suc z)) (ys 0) xs (hq 1) (twoValue xs) (hq 0)
  have hw := binaryRecover InternalListCodec.consCode frameQ (.projection 2)
    (ys 2) (ys 1) work xs (hq 2) (hq 1) (projectionValue 2 xs)
  have hr := binaryRecover InternalListCodec.consCode (.projection 3) (.projection 4)
    (ys 3) value results xs (hq 3) (projectionValue 3 xs) (projectionValue 4 xs)
  have hi := binaryRecover InternalPairing.pairing workQ resultsQ
    (ys 4) (ys 2) (ys 3) xs (hq 4) (hq 2) (hq 3)
  have ho := binaryRecover InternalPairing.pairing (InternalLessThan.constantOne 5) oldPairQ
    state (suc z) (ys 4) xs hs (InternalLessThanSupportProof.oneConstantValue xs) (hq 4)
  have hstatus := pairLeft state (suc z) (ys 4) ho
  have hinner := pairRight state (suc z) (ys 4) ho
  have hwork := unaryValue InternalUnpair.left InternalUnpair.right (ys 2) (ys 4) ss
    (pairLeft (ys 4) (ys 2) (ys 3) hi) hinner
  have hresults := unaryValue InternalUnpair.right InternalUnpair.right (ys 3) (ys 4) ss
    (pairRight (ys 4) (ys 2) (ys 3) hi) hinner
  have hdw := InternalListCodecSupportProof.consDestruction (ys 2) (ys 1) work hw
  have hframe := unaryValue InternalListCodec.headCode InternalApplicationResultStack.work
    (ys 1) (ys 2) ss (andLeft hdw) hwork
  have hrest := unaryValue InternalListCodec.tailCode InternalApplicationResultStack.work
    work (ys 2) ss (andLeft (andRight hdw)) hwork
  have htag := unaryValue InternalUnpair.left currentFrame (suc (suc z)) (ys 1) ss
    (pairLeft (ys 1) (suc (suc z)) (ys 0) hf) hframe
  have hvalue := unaryValue InternalUnpair.right currentFrame (ys 0) (ys 1) ss
    (pairRight (ys 1) (suc (suc z)) (ys 0) hf) hframe
  have hdom := unaryValue InternalUnpair.left currentValue d (ys 0) ss (pairLeft (ys 0) d e ht) hvalue
  have hcod := unaryValue InternalUnpair.right currentValue e (ys 0) ss (pairRight (ys 0) d e ht) hvalue
  have hdr := InternalListCodecSupportProof.consDestruction (ys 3) value results hr
  have hbody := unaryValue InternalListCodec.headCode InternalApplicationResultStack.results
    value (ys 3) ss (andLeft hdr) hresults
  have hremaining := unaryValue InternalListCodec.tailCode InternalApplicationResultStack.results
    results (ys 3) ss (andLeft (andRight hdr)) hresults
  have hc : Nonempty (Derivation body Gamma (graph1
      (.composition OriginalLambdaConstructor.constructor
        ![leftOf OriginalLambdaTraversal.framePayload,rightOf OriginalLambdaTraversal.framePayload,
          headOf InternalApplicationResultStack.results]) (ys 5) state)) := by
    apply compositionValue OriginalLambdaConstructor.constructor _ (ys 5) ss ![d,e,value]
      ((returnFromQueries d e work value results ys hq).1)
    intro i
    exact Fin.cases hdom (Fin.cases hcod (Fin.cases hbody (fun k => Fin.elim0 k))) i
  have hnr := binaryRecover InternalListCodec.consCode constructorQ (.projection 4)
    (ys 6) (ys 5) results xs (hq 6) (hq 5) (projectionValue 4 xs)
  have hnp := binaryRecover InternalPairing.pairing (.projection 2) newResultsQ
    (ys 7) work (ys 6) xs (hq 7) (projectionValue 2 xs) (hq 6)
  have hns := binaryRecover InternalPairing.pairing (InternalLessThan.constantOne 5) newPairQ
    (ys 8) (suc z) (ys 7) xs (hq 8) (InternalLessThanSupportProof.oneConstantValue xs) (hq 7)
  have hrl := binaryValue InternalListCodec.consCode (.composition OriginalLambdaConstructor.constructor ![leftOf OriginalLambdaTraversal.framePayload,rightOf OriginalLambdaTraversal.framePayload,headOf InternalApplicationResultStack.results])
    (tailOf InternalApplicationResultStack.results) (ys 6) (ys 5) results ss hnr hc hremaining
  have hnewpair := binaryValue InternalPairing.pairing rest
    (consOf (.composition OriginalLambdaConstructor.constructor ![leftOf OriginalLambdaTraversal.framePayload,rightOf OriginalLambdaTraversal.framePayload,headOf InternalApplicationResultStack.results]) (tailOf InternalApplicationResultStack.results))
    (ys 7) work (ys 6) ss hnp hrest hrl
  have hreturned : Nonempty (Derivation body Gamma (graph1 OriginalLambdaTraversal.lambdaReturned (ys 8) state)) :=
    binaryValue InternalPairing.pairing _ _ (ys 8) (suc z) (ys 7) ss hns
      (InternalLessThanSupportProof.oneConstantValue ss) hnewpair
  have hstatusOne := sameAccept status (InternalLessThan.constantOne 1) (suc z) ss hstatus
    (InternalLessThanSupportProof.oneConstantValue ss)
  have htagTwo := sameAccept frameTag (two 1) (suc (suc z)) ss htag (twoValue ss)
  have htagNotOne := binaryValue InternalEqualityTest.equalityTest frameTag (InternalLessThan.constantOne 1)
    z (suc (suc z)) (suc z) ss
    (InternalEqualityTestCompositionProof.rejectBackwardGap (suc (suc z)) (suc z) z
      ⟨trans (InternalAdditionLawsProof.leftSuccessor z (suc z))
        (congSuc (InternalAdditionLawsProof.leftZero (suc z)))⟩)
    htag (InternalLessThanSupportProof.oneConstantValue ss)
  have htagNotZero := binaryValue InternalEqualityTest.equalityTest frameTag (InternalAcceptance.constantZero 1)
    z (suc (suc z)) z ss
    (InternalEqualityTestCompositionProof.rejectBackwardGap (suc (suc z)) z (suc z)
      ⟨InternalAdditionLawsProof.leftZero (suc (suc z))⟩)
    htag (InternalLessThanSupportProof.zeroConstantValue ss)
  apply successorBranchIntro _ _ _ (ys 8) z ss hstatusOne
  apply nonzeroBranchIntro _ _ _ (ys 8) (ys 2) ss hwork (by simpa only [equalEqn] using (andRight (andRight hdw)))
  apply zeroBranchIntro _ _ _ (ys 8) ss htagNotZero
  apply zeroBranchIntro _ _ _ (ys 8) ss htagNotOne
  apply successorBranchIntro _ _ _ (ys 8) z ss htagTwo
  exact nonzeroBranchIntro _ _ _ (ys 8) (ys 3) ss hresults
    (by simpa only [equalEqn] using (andRight (andRight hdr))) hreturned

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalReturnLambdaProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalReturnLambdaProof
