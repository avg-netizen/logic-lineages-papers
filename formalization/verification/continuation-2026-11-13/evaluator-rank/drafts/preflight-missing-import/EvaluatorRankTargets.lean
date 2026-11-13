module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorRankDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorRankTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalTagArithmeticSyntaxProof (eqn)
/-- Source-restricted rank determinacy on one actual evaluator fibre, at the SAME
parameter. Both source admissions and both raw-rank graphs are explicit. No
structural-key equality, fold agreement, canonical fixedness, memo correctness,
or native semantic premise is assumed or concluded. -/
def ActualRankDeterminacy : Prop :=
 ∀ (R : Program 2) (H G : Program 1) (M W : Program 2)
 (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (left right parameter code leftRank rightRank : OTerm alpha),
 Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) left parameter)) →
 Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) right parameter)) →
 Nonempty (Derivation body Delta (graph2 (OriginalHereditaryEvaluatorDefinitions.evaluator R) code left parameter)) →
 Nonempty (Derivation body Delta (graph2 (OriginalHereditaryEvaluatorDefinitions.evaluator R) code right parameter)) →
 Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankPackedRaw leftRank left)) →
 Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankPackedRaw rightRank right)) →
 Nonempty (Derivation body Delta (eqn leftRank rightRank))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorRankTargets
