module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedTraceConsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedTraceLambdaBranchProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedTraceApplicationBranchProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedTraceTransportAssemblyProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedTraceTransportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalMixedClosedTraceInductionDefinitions
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem rows (H G : Program 1) (M W : Program 2) (oldStep : Program 4) (window : Program 1)
 (path : OTerm alpha) : Nonempty (Derivation body Delta
  (AtPath (OriginalTransparentMixedDirectBottom.source H G M W)
   (OriginalTransparentMixedDirectBottom.leaf H G M W oldStep) (OriginalMixedClosedTraceDefinitions.checker H G M W oldStep window) path)) := by
 apply OriginalMixedClosedTraceInductionRowsProof.rowsFromCore
 intro beta Theta code s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT hi hf
 apply OriginalMixedClosedTraceInductionAssemblyProof.atCore H G M W oldStep window
  _ code s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT hi hf
 intro xi Xi code head tail s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT hi hc hf
 exact OriginalMixedClosedTraceConsProof.atConsGeneric
  (OriginalTransparentMixedDirectBottom.source H G M W)
  (OriginalTransparentMixedDirectBottom.leaf H G M W oldStep) (OriginalMixedClosedTraceDefinitions.checker H G M W oldStep window)
  (fun beta Theta path head tail s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT next out hi hc hf hg hl hr hz =>
    OriginalMixedClosedTraceLambdaBranchProof.lambdaBranch H G M W oldStep window
     path head tail s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT next out hi hc hf hg hl hr hz)
  (fun beta Theta path head tail s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT next out hi hc hf hg hl hr hz =>
    OriginalMixedClosedTraceApplicationBranchProof.applicationBranch H G M W oldStep window
     path head tail s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT next out hi hc hf hg hl hr hz)
  code head tail s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT hi hc hf

/-- Full restricted mixed trace transport. Both concrete branch suppliers and
all smaller-path induction hypotheses are discharged here. This is not a theorem about unrecognized source edges or any old final tuple. -/
theorem actualRestrictedTransport : OriginalMixedClosedTraceTargets.ActualClosedRestrictedTransport :=
 OriginalMixedClosedTraceTransportAssemblyProof.fromRows
  (fun H G M W oldStep window body alpha Delta path => rows H G M W oldStep window path)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedTraceTransportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedTraceTransportProof
