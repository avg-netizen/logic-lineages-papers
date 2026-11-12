module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedDirectBottomTraceConsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedDirectBottomTraceLambdaBranchProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedDirectBottomTraceApplicationBranchProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedDirectBottomTraceTransportAssemblyProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedDirectBottomTraceTransportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalMixedDirectBottomTraceInductionDefinitions
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem rows (H G : Program 1) (M W : Program 2) (oldStep : Program 4)
 (path : OTerm alpha) : Nonempty (Derivation body Delta
  (AtPath (OriginalTransparentMixedDirectBottom.source H G M W)
   (OriginalTransparentMixedDirectBottom.leaf H G M W oldStep) path)) := by
 apply OriginalMixedDirectBottomTraceInductionRowsProof.rowsFromCore
 intro beta Theta code s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT hi hf
 apply OriginalMixedDirectBottomTraceInductionAssemblyProof.atCore H G M W oldStep
  _ code s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT hi hf
 intro xi Xi code head tail s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT hi hc hf
 exact OriginalMixedDirectBottomTraceConsProof.atConsGeneric
  (OriginalTransparentMixedDirectBottom.source H G M W)
  (OriginalTransparentMixedDirectBottom.leaf H G M W oldStep)
  (fun beta Theta path head tail s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT next out hi hc hf hg hl hr hz =>
    OriginalMixedDirectBottomTraceLambdaBranchProof.lambdaBranch H G M W oldStep
     path head tail s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT next out hi hc hf hg hl hr hz)
  (fun beta Theta path head tail s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT next out hi hc hf hg hl hr hz =>
    OriginalMixedDirectBottomTraceApplicationBranchProof.applicationBranch H G M W oldStep
     path head tail s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT next out hi hc hf hg hl hr hz)
  code head tail s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT hi hc hf

/-- Full restricted mixed trace transport. Both concrete branch suppliers and
all smaller-path induction hypotheses are discharged here. This is not a theorem about unrecognized source edges or any old final tuple. -/
theorem actualRestrictedTransport : OriginalMixedDirectBottomTraceTransportTargets.ActualRestrictedTransport :=
 OriginalMixedDirectBottomTraceTransportAssemblyProof.fromRows
  (fun H G M W oldStep body alpha Delta path => rows H G M W oldStep path)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedDirectBottomTraceTransportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedDirectBottomTraceTransportProof
