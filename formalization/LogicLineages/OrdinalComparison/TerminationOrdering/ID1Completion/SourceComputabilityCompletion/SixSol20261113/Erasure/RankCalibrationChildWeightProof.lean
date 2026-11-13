module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationInductionBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankMemoWeightProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationChildWeightProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalApplicationStepPeelSupportProof (andIntro)
open InternalTagArithmeticSyntaxProof (suc)
open SourceComputabilityFormulaSupportProof (numeral)
open RankMemoDefinitions
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
/-- Local strong-induction use. The child decoder equation is derived, not
assumed; original source admission and the strict numeric descent remain the
constructor-specific obligations. -/
theorem actualChildWeight (R : Program 2) (H G : Program 1) (M W : Program 2)
 (stage tab packed parameter child rank typed typ : OTerm alpha)
 (ih : Nonempty (Derivation body Delta
   (RankCalibrationInductionDefinitions.BelowRaw R H G M W (suc stage))))
 (hs : Nonempty (Derivation body Delta
   (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) packed parameter)))
 (he : Nonempty (Derivation body Delta
   (graph2 (OriginalHereditaryEvaluatorDefinitions.evaluator R) child packed parameter)))
 (hr : Nonempty (Derivation body Delta
   (graph1 OriginalRawSyntaxTransport.variableRankPackedRaw rank packed)))
 (hb : Nonempty (Derivation body Delta (InternalLessThan.strictLess child (suc stage))))
 (ht : Nonempty (Derivation body Delta (graph1 table tab stage)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed typ child))) :
 Nonempty (Derivation body Delta (programGraph lookupWeight rank
   (Fin.cons typed (Fin.cons stage (Fin.cons tab Fin.elim0))))) := by
 have hd := RankCalibrationInductionBindingProof.belowRawApply R H G M W
   (suc stage) child packed parameter rank ih hb (andIntro hs (andIntro he hr))
 exact RankMemoWeightProof.actualWeight stage tab typed typ child rank ht hb hd hp
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationChildWeightProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationChildWeightProof
