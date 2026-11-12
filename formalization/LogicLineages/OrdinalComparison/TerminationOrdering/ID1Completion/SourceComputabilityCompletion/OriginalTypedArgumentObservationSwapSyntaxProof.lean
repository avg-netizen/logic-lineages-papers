module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationSwapTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsInternalConsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsReverseInternalQuerySyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationSwapSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalTagArithmeticSyntaxProof (z zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalTypedArgumentObservationSwapDefinitions
variable {alpha beta : Type}
theorem geometryRename (sigma tau q r rawTail rawY rawX sourceRaw targetRaw : OTerm alpha) (rho : alpha → beta) :
 (Geometry sigma tau q r rawTail rawY rawX sourceRaw targetRaw).relabel rho = Geometry (sigma.relabel rho) (tau.relabel rho) (q.relabel rho) (r.relabel rho) (rawTail.relabel rho) (rawY.relabel rho) (rawX.relabel rho) (sourceRaw.relabel rho) (targetRaw.relabel rho) := by
 simp only [Geometry,InternalRecursionGraphStepSyntaxProof.conjunctionRename,graph2Rename,graph3Rename,zRelabel]
theorem childrenRename (R : Program 2) (sigma tau q r packedQ packedR valueQ valueR typedQ typedR parameter : OTerm alpha) (rho : alpha → beta) :
 (Children R sigma tau q r packedQ packedR valueQ valueR typedQ typedR parameter).relabel rho = Children R (sigma.relabel rho) (tau.relabel rho) (q.relabel rho) (r.relabel rho) (packedQ.relabel rho) (packedR.relabel rho) (valueQ.relabel rho) (valueR.relabel rho) (typedQ.relabel rho) (typedR.relabel rho) (parameter.relabel rho) := by
 simp only [Children,InternalRecursionGraphStepSyntaxProof.conjunctionRename,graph2Rename,graph3Rename,zRelabel]
theorem outputsRename (R : Program 2) (rawTail sourceRaw targetRaw observedTail source target parameter : OTerm alpha) (rho : alpha → beta) :
 (Outputs R rawTail sourceRaw targetRaw observedTail source target parameter).relabel rho = Outputs R (rawTail.relabel rho) (sourceRaw.relabel rho) (targetRaw.relabel rho) (observedTail.relabel rho) (source.relabel rho) (target.relabel rho) (parameter.relabel rho) := by
 simp only [Outputs,InternalRecursionGraphStepSyntaxProof.conjunctionRename,graph2Rename,graph3Rename,zRelabel]
theorem certificateRename (typedQ typedR observedTail rest payload certificate : OTerm alpha) (rho : alpha → beta) :
 (Certificate typedQ typedR observedTail rest payload certificate).relabel rho = Certificate (typedQ.relabel rho) (typedR.relabel rho) (observedTail.relabel rho) (rest.relabel rho) (payload.relabel rho) (certificate.relabel rho) := by
 simp only [Certificate,InternalRecursionGraphStepSyntaxProof.conjunctionRename,graph2Rename,graph3Rename,zRelabel]
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationSwapSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationSwapSyntaxProof
