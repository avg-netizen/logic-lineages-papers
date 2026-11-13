module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankMemoTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationInductionDefinitions
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- The induction index is FULL evaluator code, not native syntax or a new fuel. -/
def fields {alpha : Type} (R : Program 2) (H G : Program 1) (M W : Program 2)
 (code packed parameter rank : OTerm alpha) : Formula alpha :=
 graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) packed parameter ⊓
 (graph2 (OriginalHereditaryEvaluatorDefinitions.evaluator R) code packed parameter ⊓
 graph1 OriginalRawSyntaxTransport.variableRankPackedRaw rank packed)
def matrix {alpha : Type} (R : Program 2) (H G : Program 1) (M W : Program 2)
 (code : OTerm alpha) : Formula (alpha ⊕ Fin 3) :=
 (fields R H G M W (code.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2))).imp
 (graph1 RankMemoDefinitions.decoder (.var (.inr 2)) (code.relabel Sum.inl))
def AtRaw {alpha : Type} (R : Program 2) (H G : Program 1) (M W : Program 2)
 (code : OTerm alpha) : Formula alpha := InternalClosedPrograms.allBlock (matrix R H G M W code)
def rawPredicate {alpha : Type} (R : Program 2) (H G : Program 1) (M W : Program 2) : Formula (alpha ⊕ Fin 1) :=
 AtRaw R H G M W (.var (.inr 0))
def BelowRaw {alpha : Type} (R : Program 2) (H G : Program 1) (M W : Program 2)
 (code : OTerm alpha) : Formula alpha := InternalStrongInduction.below (rawPredicate R H G M W) code
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationInductionDefinitions
