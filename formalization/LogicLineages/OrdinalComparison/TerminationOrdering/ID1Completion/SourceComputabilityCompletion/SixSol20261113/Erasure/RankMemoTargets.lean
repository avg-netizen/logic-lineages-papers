module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankMemoDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankMemoTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open InternalTagArithmeticSyntaxProof (z suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open RankMemoDefinitions
/-- Literal total fallback only; not a source-admitted zero example. -/
def ActualZero : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha)),
 Nonempty (Derivation body Delta (graph1 decoder (numeral 1) (z : OTerm alpha)))
/-- Actual original PR table recurrence. No memo lookup correctness premise. -/
def ActualNext : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (stage old value next : OTerm alpha),
 Nonempty (Derivation body Delta (graph1 table old stage)) →
 Nonempty (Derivation body Delta (graph2 nextValue value stage old)) →
 Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode next value old)) →
 Nonempty (Derivation body Delta (graph1 table next (suc stage)))
/-- All computed earlier cells remain accessible at the actual subtraction
index stage-child, newest first. This is numerical table coherence, not a
native semantic premise or a claim that decoder already computes source rank. -/
def ActualLookupCoverage : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (stage tab child rank index : OTerm alpha),
 Nonempty (Derivation body Delta (graph1 table tab stage)) →
 Nonempty (Derivation body Delta (InternalPairingSumBounds.weakBound child stage)) →
 Nonempty (Derivation body Delta (graph1 decoder rank child)) →
 Nonempty (Derivation body Delta (graph2 InternalEqualityTest.subtract index child stage)) →
 Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup rank index tab))
/-- Eventual full INTERNAL calibration endpoint. No supplied memo correctness,
child rank equation, recursion bound, native decoding, or evaluator fixed point.
This remains pending until its entire actual source/constructor proof is paid. -/
def ActualSourceRankCalibration : Prop := ∀ (R : Program 2) (H G : Program 1) (M W : Program 2)
 (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (packed parameter code rank : OTerm alpha),
 Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) packed parameter)) →
 Nonempty (Derivation body Delta (graph2 (OriginalHereditaryEvaluatorDefinitions.evaluator R) code packed parameter)) →
 Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankPackedRaw rank packed)) →
 Nonempty (Derivation body Delta (graph1 decoder rank code))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankMemoTargets
