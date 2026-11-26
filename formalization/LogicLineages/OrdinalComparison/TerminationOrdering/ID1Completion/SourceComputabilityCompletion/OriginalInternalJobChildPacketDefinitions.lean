module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobAcceptedChildrenProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalAnnotationChildBinaryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionLambdaParameterProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobAdmissibleModeProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobChildPacket
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Actual raw-cell geometry, annotation, and independent accepted request.
No supplied child acceptance is hidden in any selector. -/
def Packet {alpha : Type} (H : Program 1) (M W : Program 2)
 (index role typ raw cell parameter c gamma outRole outType outRaw outGamma outParam annotation : OTerm alpha) : Formula alpha :=
 graph2 InternalPairing.pairing cell outRaw outParam ⊓
 (graph2 InternalPairing.pairing outParam c outGamma ⊓
 (graph2 InternalPairing.pairing annotation outRole outType ⊓
 (graph4 OriginalHereditaryAnnotatedExpansion.annotation annotation index role typ raw ⊓
 OriginalInternalJobAdmissible.Admissible H M W outRole outType outRaw outGamma c)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobChildPacket
