module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryRerootInclusion.AtRunProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryRerootInclusion.AtPrimaryProof
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
    (seed parameter sourceOut candidate targetOut sourcePool targetPool : OTerm alpha)
    (d : PrimaryData T P E body Delta seed parameter sourceOut candidate targetOut sourcePool targetPool) :
    Nonempty (Derivation body Delta (PrimaryMonotonicity.included targetOut sourceOut)) := by
  apply programCases (LengthAlignedPrimary.countOfPool P) (Fin.cons candidate (Fin.cons parameter Fin.elim0)) _
  intro beta j Theta count hj hc
  rw [includedRename]
  simp only [InternalRecursionGraphStepSyntaxProof.consTermRename,emptyRename] at hc
  have d' := PrimaryDataRenameProof.rename d j Theta hj
  let c := candidate.relabel j
  let prm := parameter.relabel j
  have hr := InternalAcceptanceBranchProof.successorBranchElim T (InternalAcceptance.constantZero 2)
    (.composition (PrimaryIteration.run E) ![LengthAlignedPrimary.countOfPool P,P,.projection 0,.projection 1])
    (targetOut.relabel j) InternalTagArithmeticSyntaxProof.z ![c,prm] d'.targetAdmitted d'.targetPrimary
  have hrun : Nonempty (Derivation body Theta
      (graph4 (PrimaryIteration.run E) (targetOut.relabel j) count (targetPool.relabel j) c prm)) := by
    apply compositionRecover (PrimaryIteration.run E)
      ![LengthAlignedPrimary.countOfPool P,P,.projection 0,.projection 1]
      (targetOut.relabel j) ![c,prm] ![count,targetPool.relabel j,c,prm] hr
    intro i
    exact Fin.cases hc (Fin.cases d'.targetPoolGraph (Fin.cases (projectionValue 0 ![c,prm])
      (Fin.cases (projectionValue 1 ![c,prm]) (fun k => Fin.elim0 k)))) i
  exact AtRunProof.bound T P E (seed.relabel j) (parameter.relabel j) (sourceOut.relabel j) (candidate.relabel j) (targetOut.relabel j) (sourcePool.relabel j) (targetPool.relabel j) count d' hrun

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryRerootInclusion.AtPrimaryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryRerootInclusion.AtPrimaryProof
