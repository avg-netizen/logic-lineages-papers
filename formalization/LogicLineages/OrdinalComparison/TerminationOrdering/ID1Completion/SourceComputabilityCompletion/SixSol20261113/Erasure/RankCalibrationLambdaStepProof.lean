module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationChildWeightProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankMemoBranchValueProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ObservationDescentDirectProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationLambdaStepProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (suc)
open InternalTagArithmeticSupportProof (refl)
open SourceComputabilityFormulaSupportProof (numeral)
open RankMemoDefinitions ObservationDescentDefinitions
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
/-- Literal lambda memo step from the actual envelope and actual admitted child.
Neither a child decoder equation nor the desired parent rank is assumed. -/
theorem actualStep (R : Program 2) (H G : Program 1) (M W : Program 2)
 (stage tab base inner root rows data typed typ packed parameter child rank : OTerm alpha)
 (ih : Nonempty (Derivation body Delta
   (RankCalibrationInductionDefinitions.BelowRaw R H G M W (suc stage))))
 (ho : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing (suc stage) base inner)))
 (hi : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing inner root rows)))
 (hg : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing root (numeral 1) data)))
 (hsel : Nonempty (Derivation body Delta (graph1 (select (directPath .lambdaBody)) typed data)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed typ child)))
 (hs : Nonempty (Derivation body Delta
   (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) packed parameter)))
 (he : Nonempty (Derivation body Delta
   (graph2 (OriginalHereditaryEvaluatorDefinitions.evaluator R) child packed parameter)))
 (hr : Nonempty (Derivation body Delta
   (graph1 OriginalRawSyntaxTransport.variableRankPackedRaw rank packed)))
 (ht : Nonempty (Derivation body Delta (graph1 table tab stage))) :
 Nonempty (Derivation body Delta (graph1 decoder rank (suc stage))) := by
 have hb := ObservationDescentDirectProof.actualDirectChildDescent .lambdaBody body alpha Delta
   (suc stage) base inner root rows data typed typ child ho hi hg hsel hp
 have hw := RankCalibrationChildWeightProof.actualChildWeight R H G M W
   stage tab packed parameter child rank typed typ ih hs he hr hb ht hp
 have hpay := RankMemoOpeningProof.payloadValue stage tab (suc stage) base inner root rows
   (numeral 1) data ⟨refl (suc stage)⟩ ho hi hg
 have htag := RankMemoOpeningProof.tagValue stage tab (suc stage) base inner root rows
   (numeral 1) data ⟨refl (suc stage)⟩ ho hi hg
 exact RankMemoSuccessorProof.atSuccessor stage tab rank ht
   (RankMemoDispatchProof.dispatch1 stage tab rank htag
     (RankMemoBranchValueProof.directValue .lambdaBody stage tab data typed rank hpay hsel hw))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationLambdaStepProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationLambdaStepProof
