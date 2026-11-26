module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionRawProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionParentProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalAnnotatedScanProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalGraphCompositionFunctionalityProof
open InternalOriginalOrderSyntaxProof
open OriginalContextInsertionSyntaxProof

theorem actualLookupDecrease : OriginalHereditaryInternalExpansionTargets.ActualLookupDecrease := by
 intro body alpha Delta parent jobs count index child W V hexp hlen hbound hlookup hw hv
 apply OriginalHereditaryInternalExpansionParentProof.expansionCases parent jobs _ hexp
 intro beta rho Theta role typ parentRaw input parameter window gamma rawJobs hrho hp hr hparam hraw hdec
 simp only [orderRename]
 have hl' := renameInto hlen rho Theta hrho
 have hb' := renameInto hbound rho Theta hrho
 have hlook' := renameInto hlookup rho Theta hrho
 have hw' := renameInto hw rho Theta hrho
 have hv' := renameInto hv rho Theta hrho
 simp only [lengthRename,OriginalContextInsertion.Below,orderRename,graph1Rename,graph2Rename] at hl' hb' hlook' hw' hv'
 apply OriginalHereditaryInternalAnnotatedScanProof.actualLookup body beta Theta
   role typ input rawJobs (jobs.relabel rho) (count.relabel rho) (index.relabel rho) (child.relabel rho)
   _ hdec hl' hb' hlook'
 intro gammaType sigma Xi rawChild hsigma hrawLength hrawLookup hcell
 simp only [orderRename]
 have hp' := renameInto hp sigma Xi hsigma
 have hr' := renameInto hr sigma Xi hsigma
 have hparam' := renameInto hparam sigma Xi hsigma
 have hraw' := renameInto hraw sigma Xi hsigma
 have hweightParent := renameInto hw' sigma Xi hsigma
 have hweightChild := renameInto hv' sigma Xi hsigma
 have hbound' := renameInto hb' sigma Xi hsigma
 simp only [graph1Rename,graph2Rename,OriginalContextInsertion.Below,orderRename] at hp' hr' hparam' hraw' hweightParent hweightChild hbound'
 have hchildForget := OriginalHereditaryInternalExpansionDecorationProof.decorateForget
   ((index.relabel rho).relabel sigma) (role.relabel sigma) (typ.relabel sigma) (input.relabel sigma)
   rawChild ((child.relabel rho).relabel sigma) hcell
 exact OriginalHereditaryInternalExpansionRawProof.rawLookupDecrease
   ((parent.relabel rho).relabel sigma) ((child.relabel rho).relabel sigma)
   (parentRaw.relabel sigma) rawChild (input.relabel sigma) (parameter.relabel sigma)
   (window.relabel sigma) (gamma.relabel sigma) ((W.relabel rho).relabel sigma) ((V.relabel rho).relabel sigma)
   (rawJobs.relabel sigma) ((count.relabel rho).relabel sigma) ((index.relabel rho).relabel sigma)
   hraw' hp' hchildForget hr' hparam' hweightParent hweightChild hrawLength hbound' hrawLookup
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionProof
