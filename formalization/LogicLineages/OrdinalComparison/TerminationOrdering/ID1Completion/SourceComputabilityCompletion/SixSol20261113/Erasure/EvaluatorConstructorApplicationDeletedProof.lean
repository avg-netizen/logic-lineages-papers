module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorInductionBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorInductionInstancesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorErasureProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPackedSourceErasureProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorApplicationDeletedProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalApplicationStepPeelSupportProof (andIntro)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open EvaluatorErasureDefinitions EvaluatorConstructorInductionDefinitions
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
/-- Substantive smaller-context step at actual queried/reconstructed application
coordinates. Source erasure and CHILD E erasure are used; parent E erasure is
not. Constructor rebuilding and length decrease are supplied as actual graph
facts by their separate adapters, never as a parent semantic equality. -/
theorem atCoordinates (R : Program 2) (H G : Program 1) (M W : Program 2)
 (left right fnLeft fnRight argLeft argRight parameter c gamma deleted deletedParameter
  cutoff d count smaller : OTerm alpha) (ys : Fin 16 → OTerm alpha)
 (hIH : Nonempty (Derivation body Delta (BelowLength R H G M W count)))
 (hLess : Nonempty (Derivation body Delta (InternalLessThan.strictLess smaller count)))
 (hsL : Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) left parameter)))
 (hsR : Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) right parameter)))
 (hf : Nonempty (Derivation body Delta (AdmittedPair R H G M W fnLeft fnRight parameter)))
 (ha : Nonempty (Derivation body Delta (AdmittedPair R H G M W argLeft argRight parameter)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c gamma)))
 (hn : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing deletedParameter c deleted)))
 (hlen : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph count gamma)))
 (hcut : Nonempty (Derivation body Delta (OriginalContextInsertion.Below cutoff count)))
 (hlook : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup d cutoff gamma)))
 (hdel : Nonempty (Derivation body Delta (graph2 OriginalClassContextAllPositionObserver.deleteAt deleted cutoff gamma)))
 (hins : Nonempty (Derivation body Delta (OriginalContextInsertion.Insert d cutoff deleted gamma)))
 (he0 : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.erasePackedRaw (ys 0) d cutoff left)))
 (he1 : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.erasePackedRaw (ys 1) d cutoff right)))
 (he2 : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.erasePackedRaw (ys 2) d cutoff fnLeft)))
 (he3 : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.erasePackedRaw (ys 3) d cutoff fnRight)))
 (he4 : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.erasePackedRaw (ys 4) d cutoff argLeft)))
 (he5 : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.erasePackedRaw (ys 5) d cutoff argRight)))
 (hcL : Nonempty (Derivation body Delta (InternalApplicationValidityClosure.applicationConstructors (ys 6) (ys 7) (ys 8) (ys 9) (ys 11) (ys 2) (ys 4) (ys 0))))
 (hcR : Nonempty (Derivation body Delta (InternalApplicationValidityClosure.applicationConstructors (ys 6) (ys 7) (ys 8) (ys 10) (ys 12) (ys 3) (ys 5) (ys 1))))
 (hnewLen : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph smaller deleted)))
 (h13 : ys 13 = deletedParameter) (h14 : ys 14 = c) (h15 : ys 15 = deleted) :
 Nonempty (Derivation body Delta (AdmittedPair R H G M W (ys 0) (ys 1) deletedParameter)) := by
 have sl := OriginalPackedSourceErasureProof.actualOriginalPackedSourceErasure body alpha Delta H G M W
   left (ys 0) d cutoff deleted gamma c parameter deletedParameter hins he0 hp hn hsL
 have sr := OriginalPackedSourceErasureProof.actualOriginalPackedSourceErasure body alpha Delta H G M W
   right (ys 1) d cutoff deleted gamma c parameter deletedParameter hins he1 hp hn hsR
 have ff := EvaluatorErasureProof.actualErasureCongruence R H G M W body alpha Delta
   fnLeft fnRight (ys 2) (ys 3) parameter deletedParameter c gamma deleted count cutoff d
   hf hp hn hlen hcut hlook hdel he2 he3
 have aa := EvaluatorErasureProof.actualErasureCongruence R H G M W body alpha Delta
   argLeft argRight (ys 4) (ys 5) parameter deletedParameter c gamma deleted count cutoff d
   ha hp hn hlen hcut hlook hdel he4 he5
 have ih := EvaluatorConstructorInductionBindingProof.belowLengthAt R H G M W count smaller hIH hLess
 have fields : Nonempty (Derivation body Delta (applicationFields R H G M W smaller ys)) := by
  unfold applicationFields
  rw [h13,h14,h15]
  exact andIntro sl (andIntro sr (andIntro hcL (andIntro hcR
    (andIntro ff (andIntro aa (andIntro hn hnewLen))))))
 have result := EvaluatorConstructorInductionInstancesProof.applicationApply R H G M W smaller ys ih fields
 simpa only [h13] using result
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorApplicationDeletedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorApplicationDeletedProof
