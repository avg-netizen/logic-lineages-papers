module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.FramedContentTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.FramedCompletionTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.FramedContentInductionDefinitions
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalClosedPrograms (allBlock)
open InternalOriginalOrderSyntaxProof (ltF)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Internal arithmetic induction row for original admitted jobs of lower weight.
Only actual framed-run content is asserted; no native Expected predicate. -/
def belowMatrix {alpha : Type} (R : Program 2) (H : Program 1) (M W : Program 2)
 (c B bound : OTerm alpha) : Formula (alpha ⊕ Fin 2) :=
 (OriginalHereditaryInternalAgenda.Job H M W (c.relabel Sum.inl) (B.relabel Sum.inl) (.var (.inr 0)) ⊓
  (graph1 OriginalHereditaryFuelProgram.weight (.var (.inr 1)) (.var (.inr 0)) ⊓
   ltF (.var (.inr 1)) (bound.relabel Sum.inl))).imp
 (FramedContentDefinitions.AllFramedContent R (.var (.inr 0)))
def BelowContent {alpha : Type} (R : Program 2) (H : Program 1) (M W : Program 2)
 (c B bound : OTerm alpha) : Formula alpha :=
 allBlock (belowMatrix R H M W c B bound)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.FramedContentInductionDefinitions
