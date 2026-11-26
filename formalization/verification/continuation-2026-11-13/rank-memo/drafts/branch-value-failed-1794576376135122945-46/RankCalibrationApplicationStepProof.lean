module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationChildWeightProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankMemoBranchValueProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ObservationDescentDirectProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationApplicationStepProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (suc)
open InternalTagArithmeticSupportProof (refl)
open SourceComputabilityFormulaSupportProof (numeral)
open RankMemoDefinitions ObservationDescentDefinitions
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
/-- Both actual application children are calibrated at their strict smaller
full evaluator codes; the memo's actual addition branch combines their ranks. -/
theorem actualStep (R : Program 2) (H G : Program 1) (M W : Program 2)
 (stage tab base inner root rows data : OTerm alpha)
 (ftyped ftyp fpacked fparameter fchild frank atyped atyp apacked aparameter achild arank : OTerm alpha)
 (ih : Nonempty (Derivation body Delta
   (RankCalibrationInductionDefinitions.BelowRaw R H G M W (suc stage))))
 (ho : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing (suc stage) base inner)))
 (hi : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing inner root rows)))
 (hg : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing root (numeral 2) data)))
 (hfsel : Nonempty (Derivation body Delta (graph1 (select (directPath .function)) ftyped data)))
 (hfp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing ftyped ftyp fchild)))
 (hfs : Nonempty (Derivation body Delta
   (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) fpacked fparameter)))
 (hfe : Nonempty (Derivation body Delta
   (graph2 (OriginalHereditaryEvaluatorDefinitions.evaluator R) fchild fpacked fparameter)))
 (hfr : Nonempty (Derivation body Delta
   (graph1 OriginalRawSyntaxTransport.variableRankPackedRaw frank fpacked)))
 (hasel : Nonempty (Derivation body Delta (graph1 (select (directPath .argument)) atyped data)))
 (hap : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing atyped atyp achild)))
 (has : Nonempty (Derivation body Delta
   (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) apacked aparameter)))
 (hae : Nonempty (Derivation body Delta
   (graph2 (OriginalHereditaryEvaluatorDefinitions.evaluator R) achild apacked aparameter)))
 (har : Nonempty (Derivation body Delta
   (graph1 OriginalRawSyntaxTransport.variableRankPackedRaw arank apacked)))
 (ht : Nonempty (Derivation body Delta (graph1 table tab stage))) :
 Nonempty (Derivation body Delta (graph1 decoder (InternalTagArithmeticSyntaxProof.add frank arank) (suc stage))) := by
 have hpay := RankMemoOpeningProof.payloadValue stage tab (suc stage) base inner root rows
   (numeral 2) data ⟨refl (suc stage)⟩ ho hi hg
 have htag := RankMemoOpeningProof.tagValue stage tab (suc stage) base inner root rows
   (numeral 2) data ⟨refl (suc stage)⟩ ho hi hg
 have hfb := ObservationDescentDirectProof.actualDirectChildDescent .function body alpha Delta
   (suc stage) base inner root rows data ftyped ftyp fchild ho hi hg hfsel hfp
 have hfw := RankCalibrationChildWeightProof.actualChildWeight R H G M W
   stage tab fpacked fparameter fchild frank ftyped ftyp ih hfs hfe hfr hfb ht hfp
 have hfv := RankMemoBranchValueProof.directValue .function stage tab data ftyped frank hpay hfsel hfw
 have hab := ObservationDescentDirectProof.actualDirectChildDescent .argument body alpha Delta
   (suc stage) base inner root rows data atyped atyp achild ho hi hg hasel hap
 have haw := RankCalibrationChildWeightProof.actualChildWeight R H G M W
   stage tab apacked aparameter achild arank atyped atyp ih has hae har hab ht hap
 have hav := RankMemoBranchValueProof.directValue .argument stage tab data atyped arank hpay hasel haw
 exact RankMemoSuccessorProof.atSuccessor stage tab (InternalTagArithmeticSyntaxProof.add frank arank) ht
   (RankMemoDispatchProof.dispatch2 stage tab (InternalTagArithmeticSyntaxProof.add frank arank) htag
     (RankMemoBranchValueProof.sumValue (directRank .function) (directRank .argument) stage tab frank arank hfv hav))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationApplicationStepProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationApplicationStepProof
