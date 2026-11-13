module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankMemoDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorRankDefinitions
open FirstOrder Language PositiveArithmeticOperators InternalCalculus
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Original source-admitted fibre of the unchanged hereditary evaluator at one
actual parameter and actual output code. This does not replace a structural key. -/
def Fibre {alpha : Type} (R : Program 2) (H G : Program 1) (M W : Program 2)
 (packed parameter code : OTerm alpha) : Formula alpha :=
 (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) packed parameter) ⊓
 (graph2 (OriginalHereditaryEvaluatorDefinitions.evaluator R) code packed parameter)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorRankDefinitions
