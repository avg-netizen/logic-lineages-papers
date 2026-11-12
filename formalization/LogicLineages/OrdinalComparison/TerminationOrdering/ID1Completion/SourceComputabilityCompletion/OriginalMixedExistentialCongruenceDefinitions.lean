module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMixedDirectBottomDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalExistentialRankResultDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedExistentialCongruenceDefinitions
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Transformed application geometry, independent of any certificate. The exact shared argument and all discarded outer types are retained. -/
def ApplicationFrame {alpha : Type} (source : Program 2)
 (s t parameter childS childT arg d e arrow : OTerm alpha) : Formula alpha :=
 graph2 source InternalOriginalStepGuard.one s parameter ⊓
 (graph4 application s d e childS arg ⊓
 (graph4 application t d e childT arg ⊓
 (graph2 InternalListCodec.consCode arrow d e ⊓
 (graph1 InternalUnpair.left arrow childS ⊓
 (graph1 InternalUnpair.left arrow childT ⊓ graph1 InternalUnpair.left d arg)))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedExistentialCongruenceDefinitions
