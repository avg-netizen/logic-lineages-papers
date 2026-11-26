module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedDirectBottomTraceTransportTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionInternalDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedTraceValidityDefinitions
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
def fields {alpha : Type} (source : Program 2) (leaf : Program 4)
 (path s t cert oldParam : OTerm alpha) : Formula alpha :=
 graph1 InternalUnpair.left path cert ⊓
 (graph2 source (numeral 1) s oldParam ⊓
  graph4 (OriginalMixedDirectBottomTrace.recognizes source leaf) (numeral 1) s t cert oldParam)
def result {alpha : Type} (source : Program 2) (leaf : Program 4)
 (t oldParam : OTerm alpha) : Formula alpha := graph2 source (numeral 1) t oldParam
/-- Four runtime coordinates remain internally universally bound. -/
def matrix {alpha : Type} (source : Program 2) (leaf : Program 4) (path : OTerm alpha) : Formula (alpha ⊕ Fin 4) :=
 (fields source leaf (path.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2)) (.var (.inr 3))).imp
 (result source leaf (.var (.inr 1)) (.var (.inr 3)))
def AtPath {alpha : Type} (source : Program 2) (leaf : Program 4) (path : OTerm alpha) : Formula alpha :=
 InternalClosedPrograms.allBlock (matrix source leaf path)
def pathPredicate {alpha : Type} (source : Program 2) (leaf : Program 4) : Formula (alpha ⊕ Fin 1) :=
 AtPath source leaf (.var (.inr 0))
def BelowPath {alpha : Type} (source : Program 2) (leaf : Program 4) (path : OTerm alpha) : Formula alpha :=
 InternalStrongInduction.below (pathPredicate source leaf) path
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedTraceValidityDefinitions
