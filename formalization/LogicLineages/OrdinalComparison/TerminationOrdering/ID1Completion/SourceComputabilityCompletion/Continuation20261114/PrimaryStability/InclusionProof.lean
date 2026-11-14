module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryStability.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryMonotonicity.StepProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryStability.InclusionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof InternalTagArithmeticSyntaxProof
open InternalTagArithmeticSupportProof SourceComputabilityFormulaSupportProof
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open InternalApplicationStepPeelSupportProof (andIntro)
open InternalBetaTotalityProof InternalQuotientComparisonProof
open TwoSol20261113.CalibratedPrimary.Membership
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

open PrimaryMonotonicity.InclusionProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem reflexive (raw : OTerm alpha) :
    Nonempty (Derivation body Delta (PrimaryMonotonicity.included raw raw)) := by
  apply introduce raw raw
  intro beta j Theta candidate hj hm
  exact hm

theorem transitive (left middle right : OTerm alpha)
    (hl : Nonempty (Derivation body Delta (PrimaryMonotonicity.included left middle)))
    (hr : Nonempty (Derivation body Delta (PrimaryMonotonicity.included middle right))) :
    Nonempty (Derivation body Delta (PrimaryMonotonicity.included left right)) := by
  apply introduce left right
  intro beta j Theta candidate hj hm
  have hl' := renameInto hl j Theta hj
  have hr' := renameInto hr j Theta hj
  rw [includedRename] at hl' hr'
  exact eliminate (middle.relabel j) (right.relabel j) candidate hr'
    (eliminate (left.relabel j) (middle.relabel j) candidate hl' hm)

theorem expansionIncluded (E : Program 3) (pool before after parameter : OTerm alpha)
    (he : Nonempty (Derivation body Delta (graph3 (PrimaryExpansion.expand E) after pool before parameter))) :
    Nonempty (Derivation body Delta (PrimaryMonotonicity.included before after)) := by
  apply introduce before after
  intro beta j Theta candidate hj hm
  have he' := renameInto he j Theta hj
  rw [graph3Rename] at he'
  exact PrimaryExpansion.PreservationProof.internalPreservation E body beta Theta
    (pool.relabel j) (before.relabel j) (parameter.relabel j) (after.relabel j) candidate he' hm

theorem successorStability : Targets.SuccessorStability := by
  intro E body alpha Delta pool before after next parameter hbefore hafter hi
  exact PrimaryMonotonicity.StepProof.expansionMonotonicity E body alpha Delta
    pool after before parameter next after hi hafter hbefore

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryStability.InclusionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryStability.InclusionProof
