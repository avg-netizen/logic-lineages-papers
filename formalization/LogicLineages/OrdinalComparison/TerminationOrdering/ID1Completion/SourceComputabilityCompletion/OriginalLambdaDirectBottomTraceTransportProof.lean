module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceConsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceTransportAssemblyProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomGlobalInternalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceTransportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalLambdaDirectBottomTraceInductionDefinitions
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem actualCons (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
 (path head tail s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowPath (OriginalTransparentDirectBottomGlobal.source p H G W)
   (OriginalTransparentDirectBottomGlobal.finalInputs p H G W P).oldStep path)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode path head tail)))
 (hf : Nonempty (Derivation body Delta (fields (OriginalTransparentDirectBottomGlobal.source p H G W)
   (OriginalTransparentDirectBottomGlobal.finalInputs p H G W P).oldStep path
   s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT))) :
 Nonempty (Derivation body Delta (result (OriginalTransparentDirectBottomGlobal.source p H G W)
   (OriginalTransparentDirectBottomGlobal.finalInputs p H G W P).oldStep s t newParam erasedS erasedT)) := by
 rw [OriginalTransparentDirectBottomGlobalInternalProof.finalLeaf] at hi hf ⊢
 let b := OriginalTransparentDirectBottomGlobal.initial p H G W
 let r := OriginalTransparentLambdaStepGlobal.refined b H G W P
 exact OriginalLambdaDirectBottomTraceConsProof.atCons H G
   (InternalOriginalUniformContextMembership.contextMember p.base.member) W
   (OriginalHereditaryLambdaGlobal.priorFinal b).oldStep
   (OriginalHereditaryLambdaGlobal.endpoint (OriginalLambdaTraversalSelection.prepareInputs r)) r.window
   path head tail s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT hi hc hf

theorem actualRows (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
 (path : OTerm alpha) : Nonempty (Derivation body Delta
  (AtPath (OriginalTransparentDirectBottomGlobal.source p H G W)
   (OriginalTransparentDirectBottomGlobal.finalInputs p H G W P).oldStep path)) := by
 apply OriginalLambdaDirectBottomTraceInductionRowsProof.rowsFromCore
 intro beta Theta code s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT hi hf
 exact OriginalLambdaDirectBottomTraceInductionAssemblyProof.atCore p H G W P
   (fun beta Theta path head tail s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT hi hc hf =>
     actualCons p H G W P path head tail s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT hi hc hf)
   code s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT hi hf

theorem actualRestrictedTransport : OriginalLambdaDirectBottomTraceTransportTargets.ActualRestrictedTransport :=
 OriginalLambdaDirectBottomTraceTransportAssemblyProof.fromRows
   (fun p H G W P body alpha Delta path => actualRows p H G W P path)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceTransportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceTransportProof
