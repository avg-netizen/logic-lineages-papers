module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionLengthBoundProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionLengthProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalGraphCompositionFunctionalityProof
open InternalOriginalOrderSyntaxProof
open InternalTagArithmeticSyntaxProof (sucRelabel)
open OriginalContextInsertionSyntaxProof

theorem actualLengthBound : OriginalHereditaryInternalExpansionLengthTargets.ActualLengthBound := by
 intro body alpha Delta parent jobs count W he hl hw
 apply OriginalHereditaryInternalExpansionParentProof.expansionCases parent jobs _ he
 intro beta rho Theta role typ parentRaw input parameter window gamma rawJobs hrho hp hr hparam hraw hdec
 simp only [orderRename,sucRelabel]
 have hl' := renameInto hl rho Theta hrho
 have hw' := renameInto hw rho Theta hrho
 simp only [lengthRename,graph1Rename] at hl' hw'
 exact OriginalHereditaryInternalExpansionLengthBoundProof.atCoordinates
   (parent.relabel rho) parentRaw input parameter window gamma role typ rawJobs
   (jobs.relabel rho) (count.relabel rho) (W.relabel rho) hp hr hparam hraw hdec hl' hw'
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionLengthProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionLengthProof
