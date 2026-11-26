module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankMemoTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationBaseTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Original admitted variable source, arbitrary actual full evaluator code.
No IH, decoded memo-tag, positive-code, table or desired rank premise. -/
def ActualVariable : Prop := ∀ (R : Program 2) (H G : Program 1) (M W : Program 2)
 (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (packed parameter code rank : OTerm alpha),
 Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) packed parameter)) →
 Nonempty (Derivation body Delta (graph2 (OriginalHereditaryEvaluatorDefinitions.evaluator R) code packed parameter)) →
 Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankPackedRaw rank packed)) →
 Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.tag (numeral 0) packed)) →
 Nonempty (Derivation body Delta (graph1 RankMemoDefinitions.decoder rank code))

/-- Original admitted bottom source, arbitrary actual full evaluator code.
No IH, decoded memo-tag, positive-code, table or desired rank premise. -/
def ActualBottom : Prop := ∀ (R : Program 2) (H G : Program 1) (M W : Program 2)
 (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (packed parameter code rank : OTerm alpha),
 Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) packed parameter)) →
 Nonempty (Derivation body Delta (graph2 (OriginalHereditaryEvaluatorDefinitions.evaluator R) code packed parameter)) →
 Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankPackedRaw rank packed)) →
 Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.tag (numeral 3) packed)) →
 Nonempty (Derivation body Delta (graph1 RankMemoDefinitions.decoder rank code))

/-- Honest exclusion of full evaluator code zero for each nonvariable source
tag 1 through 5. Does not assert that any admitted variable has code zero. -/
def ActualNonvariableNonzero : Prop := ∀ (R : Program 2) (H G : Program 1) (M W : Program 2)
 (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (packed parameter code : OTerm alpha) (k : Fin 5),
 Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) packed parameter)) →
 Nonempty (Derivation body Delta (graph2 (OriginalHereditaryEvaluatorDefinitions.evaluator R) code packed parameter)) →
 Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.tag (numeral (k.val+1)) packed)) →
 Nonempty (Derivation body Delta ((equal code (numeral 0)).not))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationBaseTargets
