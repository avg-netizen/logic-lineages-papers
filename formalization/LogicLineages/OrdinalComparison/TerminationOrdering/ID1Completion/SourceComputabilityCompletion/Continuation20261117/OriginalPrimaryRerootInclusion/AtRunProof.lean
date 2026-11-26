module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryRerootInclusion.PrimaryDataRenameProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryRerootInclusion.ClosedRunProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryRerootInclusion.AtRunProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof InternalAcceptanceSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalTagArithmeticSyntaxProof (eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114
open TwoSol20261113.CalibratedPrimary.Membership
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InternalBetaTotalityProof (disjunctionElimination)
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open PrimaryMonotonicity.InclusionProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem bound (T P : Program 2) (E : Program 3)
    (seed parameter sourceOut candidate targetOut sourcePool targetPool count : OTerm alpha)
    (d : PrimaryData T P E body Delta seed parameter sourceOut candidate targetOut sourcePool targetPool)
    (hr : Nonempty (Derivation body Delta (graph4 (PrimaryIteration.run E) targetOut count targetPool candidate parameter))) :
    Nonempty (Derivation body Delta (PrimaryMonotonicity.included targetOut sourceOut)) := by
  apply programCases (PrimaryExpansion.expand E) (Fin.cons targetPool (Fin.cons sourceOut (Fin.cons parameter Fin.elim0))) _
  intro beta j Theta first hj he
  rw [includedRename]
  simp only [InternalRecursionGraphStepSyntaxProof.consTermRename,emptyRename] at he
  have d' := PrimaryDataRenameProof.rename d j Theta hj
  have hr' := renameInto hr j Theta hj
  rw [graph4Rename] at hr'
  have hclosed := ClosureProof.expansion T P E (seed.relabel j) (parameter.relabel j)
    (sourcePool.relabel j) (sourceOut.relabel j) (targetPool.relabel j) first
    d'.sourceAdmitted d'.sourcePoolGraph d'.sourcePrimary d'.pools he
  exact ClosedRunProof.bound E (count.relabel j) (targetPool.relabel j) (candidate.relabel j)
    (parameter.relabel j) (targetOut.relabel j) (sourceOut.relabel j) first hr' d'.member he hclosed

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryRerootInclusion.AtRunProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryRerootInclusion.AtRunProof
