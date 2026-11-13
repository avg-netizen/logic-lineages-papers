module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ExpansionMapGeometryDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFiniteBlocksDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ExpansionMapGeometryScanDefinitions
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalApplicationStepPeel (graph5)
open InternalAdditionLawsProof (add)
open InternalFiniteBlocks (block)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Existential extension row, at fixed original scan endpoints. -/
def suffixMatrix {alpha : Type} (count prefixRow full : OTerm alpha) : Formula (alpha ⊕ Fin 1) :=
 OriginalContextInsertion.lengthGraph (count.relabel Sum.inl) (.var (.inr 0)) ⊓
 graph2 InternalApplicationValidityStackAppend.append (full.relabel Sum.inl)
   (prefixRow.relabel Sum.inl) (.var (.inr 0))
def Extension {alpha : Type} (count prefixRow full : OTerm alpha) : Formula alpha :=
 block (suffixMatrix count prefixRow full)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ExpansionMapGeometryScanDefinitions
