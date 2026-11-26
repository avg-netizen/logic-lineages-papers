module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.InductionDefinitions
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.MemberTransportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open InternalTagArithmeticSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 Continuation20261115
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open Induction
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)

open TwoSol20261113.CalibratedPrimary.Membership (contains)

theorem transport (allowed source target : OTerm alpha)
    (he : Nonempty (Derivation body Delta (eqn source target)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) allowed source))) :
    Nonempty (Derivation body Delta (graph2 contains (numeral 1) allowed target)) := by
  unfold graph2 programGraph at hm ⊢
  apply InternalGraphCompositionEqualityProof.graphInputTransport body alpha 2 Delta
    (OrdinaryArithmetic.graphFormula contains) (numeral 1) ![allowed,source] ![allowed,target] _ hm
  intro i
  fin_cases i
  · rw [InternalSourceInversionSupportProof.onEquality]; exact ⟨refl allowed⟩
  · rw [InternalSourceInversionSupportProof.onEquality]; exact he

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.MemberTransportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.MemberTransportProof
