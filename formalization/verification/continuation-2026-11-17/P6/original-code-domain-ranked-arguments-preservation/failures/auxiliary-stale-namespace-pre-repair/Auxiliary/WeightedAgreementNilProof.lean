module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.CountAgreementNilProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.FoldDefinitions
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.WeightedAgreementNilProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261115.BoundsRecombination (maximum merge)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open InternalTagArithmeticSyntaxProof (z eqn)
open Continuation20261115.OriginalArgumentPermutationClosure.CountAgreement

theorem nil (weight : Program 1) (right ls rs : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (agreement z right)))
    (hl : Nonempty (Derivation body Delta (graph1 (Fold.weighted weight) ls z)))
    (hr : Nonempty (Derivation body Delta (graph1 (Fold.weighted weight) rs right))) :
    Nonempty (Derivation body Delta (eqn ls rs)) := by
  have he := CountAgreementNilProof.rightZero right ha
  have hr0 := headTransport (Fold.weighted weight) rs right z Fin.elim0 he hr
  exact valueUnique (Fold.weighted weight) ls rs ![z] hl hr0
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.WeightedAgreementNilProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.WeightedAgreementNilProof
