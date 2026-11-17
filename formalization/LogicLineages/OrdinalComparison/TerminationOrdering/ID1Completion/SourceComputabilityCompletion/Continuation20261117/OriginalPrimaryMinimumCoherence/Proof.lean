module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryMinimumCoherence.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryMinimumCoherence.LeastnessProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryClassRowCoherence.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryRerootInclusion.AdmissionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentPrimary.InternalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryMinimumCoherence.Proof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalAcceptanceBranchProof
open InternalGraphCompositionFunctionalityProof InternalGraphCompositionEqualityProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof (refl symm)
open InternalBetaTotalityProof
open InternalPositiveUnfoldingSupportProof InternalOriginalOrderSyntaxProof InternalQuotientComparisonProof
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open Continuation20261114 Continuation20261115 Continuation20261116
open SourceComputabilityFormulaSupportProof (numeral)
attribute [local irreducible] OriginalConcreteHeadSignature.signature OriginalCandidates.candidates OriginalDecodedContextValidity.contextGuard OriginalConcreteStructuralEdge.edge SeededPrimaryPool.pool

theorem minimumCoherence : Targets.InternalMinimumCoherence := by
  intro n arity body alpha Delta seed parameter typ raw context gamma types out candidate targetOut minimumOut targetMinimumOut hs hp hg ht hc ha hl hm htarget hmin htmin
  let T := OriginalTypedDecoder.target (OriginalConcreteHeadSignature.signature n arity) (OriginalDecodedContextValidity.contextGuard n)
  let Q := OriginalCandidates.candidates n arity (OriginalConcreteHeadSignature.signature n arity)
  let E := OriginalConcreteStructuralEdge.edge n arity
  let pool := SeededPrimaryPool.pool T Q
  let L := SeededPrimaryPool.primary T Q E
  let P := TwoSol20261113.CalibratedPrimary.Membership.classTest T L (TransparentCandidate.candidate T)
  let request : OriginalPrimaryRerootInclusion.Request n arity body Delta seed parameter typ raw context gamma types out candidate targetOut :=
    ⟨hs,hp,hg,ht,hc,ha,hl,hm,htarget⟩
  have had := OriginalPrimaryRerootInclusion.AdmissionProof.both n arity seed parameter typ raw context gamma types out candidate targetOut request
  have hself := TransparentPrimary.InternalProof.internalClassReflexivity T
    (LengthAlignedPrimary.countOfPool pool) pool E body alpha Delta seed parameter had.1
  have hother := TransparentPrimary.InternalProof.internalClassReflexivity T
    (LengthAlignedPrimary.countOfPool pool) pool E body alpha Delta candidate parameter had.2
  apply LeastnessProof.unique T P seed candidate minimumOut targetMinimumOut parameter
    had.1 had.2 hself hother hmin htmin
  intro probe
  exact OriginalPrimaryClassRowCoherence.Proof.classRows n arity body alpha Delta
    seed parameter typ raw context gamma types out candidate targetOut probe hs hp hg ht hc ha hl hm htarget

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryMinimumCoherence.Proof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryMinimumCoherence.Proof
