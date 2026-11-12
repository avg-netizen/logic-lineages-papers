module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMixedPathDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMixedPathInternalDefinitions
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Exact original application-function hop. Constructors discard packed
child types, so those actual types and their arrow graph are retained explicitly.
The complete unchanged argument and runtime parameter are shared. -/
def ApplicationHop {alpha : Type} (source : Program 2)
 (s t cert parameter childS childT childCert arg d e arrow : OTerm alpha) : Formula alpha :=
 graph2 source (numeral 1) s parameter ⊓
 (graph4 application s d e childS arg ⊓
 (graph4 application t d e childT arg ⊓
 (graph2 InternalListCodec.consCode arrow d e ⊓
 (graph1 InternalUnpair.left arrow childS ⊓
 (graph1 InternalUnpair.left arrow childT ⊓
 (graph1 InternalUnpair.left d arg ⊓ graph1 stepLift cert childCert))))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMixedPathInternalDefinitions
