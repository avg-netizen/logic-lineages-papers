module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryRankGuardCoherence.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryMinimumCoherence.LeastnessProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentPrimary.InternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.CandidateIntegration.Proof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryRankGuardCoherence.MinimumMemberProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalApplicationStepPeelSupportProof (andLeft andRight sameAccept)
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof (symm)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 Continuation20261115 Continuation20261116
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
theorem member (T Q : Program 2) (E : Program 3) (seed parameter out minimumOut : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph2 T (numeral 1) seed parameter)))
    (hl : Nonempty (Derivation body Delta (graph2 (SeededPrimaryPool.primary T Q E) out seed parameter)))
    (hm : Nonempty (Derivation body Delta
      (graph2 (OriginalTransparentMinimum.minimum T
        (TwoSol20261113.CalibratedPrimary.Membership.classTest T (SeededPrimaryPool.primary T Q E)
          (TransparentCandidate.candidate T))) minimumOut seed parameter))) :
    Nonempty (Derivation body Delta
      (graph2 TwoSol20261113.CalibratedPrimary.Membership.contains (numeral 1) out minimumOut)) := by
  let pool := SeededPrimaryPool.pool T Q
  let L := SeededPrimaryPool.primary T Q E
  let P := TwoSol20261113.CalibratedPrimary.Membership.classTest T L (TransparentCandidate.candidate T)
  have hself := TransparentPrimary.InternalProof.internalClassReflexivity T
    (LengthAlignedPrimary.countOfPool pool) pool E body alpha Delta seed parameter ht
  have facts := OriginalPrimaryMinimumCoherence.LeastnessProof.facts T P seed minimumOut parameter minimumOut ht hm
  have hc := OriginalPrimaryMinimumCoherence.NormalizationProof.toClass T P seed minimumOut parameter hself (andLeft (andRight facts))
  exact andRight ((CandidateIntegration.Proof.classFactor T L body alpha Delta seed minimumOut parameter out hl).mp hc)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryRankGuardCoherence.MinimumMemberProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryRankGuardCoherence.MinimumMemberProof
