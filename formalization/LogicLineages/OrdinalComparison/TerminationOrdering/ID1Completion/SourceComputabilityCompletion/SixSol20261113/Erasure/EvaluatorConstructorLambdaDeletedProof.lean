module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorApplicationDeletedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorLambdaDeletedProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalApplicationStepPeelSupportProof (andIntro)
open InternalTagArithmeticSyntaxProof (suc)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open EvaluatorErasureDefinitions EvaluatorConstructorInductionDefinitions
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
/-- Smaller-PARENT-context lambda step. Only CHILD evaluator erasure is used,
at successor cutoff and actual extended child parameters. The parent semantic
conclusion comes from the strictly smaller parent-length induction hypothesis. -/
theorem atCoordinates (R : Program 2) (H G : Program 1) (M W : Program 2)
 (left right childLeft childRight parameter childParameter c gamma deleted childGamma childDeleted
  cutoff d count smaller childCount : OTerm alpha) (ys : Fin 11 → OTerm alpha)
 (hIH : Nonempty (Derivation body Delta (BelowLength R H G M W count)))
 (hLess : Nonempty (Derivation body Delta (InternalLessThan.strictLess smaller count)))
 (hsL : Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) left parameter)))
 (hsR : Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) right parameter)))
 (hc : Nonempty (Derivation body Delta (AdmittedPair R H G M W childLeft childRight childParameter)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c gamma)))
 (hn : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing (ys 6) c deleted)))
 (hins : Nonempty (Derivation body Delta (OriginalContextInsertion.Insert d cutoff deleted gamma)))
 (hcp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing childParameter c childGamma)))
 (hcn : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing (ys 7) c childDeleted)))
 (hclen : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph childCount childGamma)))
 (hccut : Nonempty (Derivation body Delta (OriginalContextInsertion.Below (suc cutoff) childCount)))
 (hclook : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup d (suc cutoff) childGamma)))
 (hcdel : Nonempty (Derivation body Delta (graph2 OriginalClassContextAllPositionObserver.deleteAt childDeleted (suc cutoff) childGamma)))
 (he0 : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.erasePackedRaw (ys 0) d cutoff left)))
 (he1 : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.erasePackedRaw (ys 1) d cutoff right)))
 (he2 : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.erasePackedRaw (ys 2) d (suc cutoff) childLeft)))
 (he3 : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.erasePackedRaw (ys 3) d (suc cutoff) childRight)))
 (hcons : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode childDeleted (ys 4) deleted)))
 (hcL : Nonempty (Derivation body Delta (graph3 OriginalLambdaConstructor.constructor (ys 0) (ys 4) (ys 5) (ys 2))))
 (hcR : Nonempty (Derivation body Delta (graph3 OriginalLambdaConstructor.constructor (ys 1) (ys 4) (ys 5) (ys 3))))
 (htL : Nonempty (Derivation body Delta (graph1 InternalUnpair.left (ys 5) (ys 2))))
 (htR : Nonempty (Derivation body Delta (graph1 InternalUnpair.left (ys 5) (ys 3))))
 (hnewLen : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph smaller deleted)))
 (h8 : ys 8 = c) (h9 : ys 9 = deleted) (h10 : ys 10 = childDeleted) :
 Nonempty (Derivation body Delta (AdmittedPair R H G M W (ys 0) (ys 1) (ys 6))) := by
 have sl := OriginalPackedSourceErasureProof.actualOriginalPackedSourceErasure body alpha Delta H G M W
   left (ys 0) d cutoff deleted gamma c parameter (ys 6) hins he0 hp hn hsL
 have sr := OriginalPackedSourceErasureProof.actualOriginalPackedSourceErasure body alpha Delta H G M W
   right (ys 1) d cutoff deleted gamma c parameter (ys 6) hins he1 hp hn hsR
 have cc := EvaluatorErasureProof.actualErasureCongruence R H G M W body alpha Delta
   childLeft childRight (ys 2) (ys 3) childParameter (ys 7) c childGamma childDeleted childCount (suc cutoff) d
   hc hcp hcn hclen hccut hclook hcdel he2 he3
 have ih := EvaluatorConstructorInductionBindingProof.belowLengthAt R H G M W count smaller hIH hLess
 have fields : Nonempty (Derivation body Delta (lambdaFields R H G M W smaller ys)) := by
  unfold lambdaFields
  rw [h8,h9,h10]
  exact andIntro sl (andIntro sr (andIntro hn (andIntro hcons (andIntro hcn
    (andIntro hcL (andIntro hcR (andIntro htL (andIntro htR (andIntro cc hnewLen)))))))))
 exact EvaluatorConstructorInductionInstancesProof.lambdaApply R H G M W smaller ys ih fields
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorLambdaDeletedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorLambdaDeletedProof
