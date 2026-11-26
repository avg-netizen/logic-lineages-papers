module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalReturnRootProjectionSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalReturnRootProjectionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open OriginalInternalReturnRootProjectionSupportProof
open OriginalInternalDecorationCoordinatesProof (pairRecover)
theorem actualProjection : OriginalInternalReturnRootProjectionTargets.ActualProjection := by
 intro R body alpha Delta input work results frame rest payload packed parameter out outWork stack value old root tail
   hstate hwork hframe hrole hpacked hparameter hstep hout hstack hvalue
 let xs : Fin 1 → OTerm alpha := Fin.cons input Fin.elim0
 have hp := popRecover R input work results frame rest payload out hstate hwork hframe hrole hstep
 have hs := andRight (pairRecover OriginalHereditaryReturnStep.rest
   (consOf (OriginalHereditaryReturnStep.termValue R) OriginalHereditaryReturnStep.oldSuffix)
   out outWork stack xs hp hout)
 have hv := andLeft (consRecover (OriginalHereditaryReturnStep.termValue R) OriginalHereditaryReturnStep.oldSuffix stack value old xs hs hstack)
 let rootP : LogicLineages.ComputabilityKnowledge.GorbowPRProgram.Program 1 := .composition (OriginalRootObservation.rootObservation R)
   ![OriginalHereditaryReturnStep.packed,OriginalHereditaryReturnStep.parameter]
 have hr := andLeft (pairRecover rootP _ value root tail xs hv hvalue)
 exact binaryRecover (OriginalRootObservation.rootObservation R) OriginalHereditaryReturnStep.packed OriginalHereditaryReturnStep.parameter
   root packed parameter xs hr hpacked hparameter
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalReturnRootProjectionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalReturnRootProjectionProof
