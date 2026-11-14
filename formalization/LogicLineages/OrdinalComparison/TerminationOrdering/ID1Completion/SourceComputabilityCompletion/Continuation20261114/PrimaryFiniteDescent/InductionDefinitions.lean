module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryFiniteDescent.ArithmeticProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryFiniteDescent.InductionDefinitions
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

namespace Induction
def fields {alpha : Type} (E : Program 3)
    (elapsed pool initial parameter out next initialRemaining remaining : OTerm alpha) : Formula alpha :=
  graph4 (PrimaryIteration.iterate E) out elapsed pool initial parameter ⊓
    (graph3 (PrimaryExpansion.expand E) next pool out parameter ⊓
      (graph2 PrimaryUncoveredCount.count initialRemaining pool initial ⊓
        graph2 PrimaryUncoveredCount.count remaining pool out))
def matrix {alpha : Type} (E : Program 3) (elapsed : OTerm alpha) : Formula (alpha ⊕ Fin 7) :=
  (fields E (elapsed.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2))
    (.var (.inr 3)) (.var (.inr 4)) (.var (.inr 5)) (.var (.inr 6))).imp
  (budget (elapsed.relabel Sum.inl) (.var (.inr 5)) (.var (.inr 6)) (.var (.inr 3)) (.var (.inr 4)))
def AtCount {alpha : Type} (E : Program 3) (elapsed : OTerm alpha) : Formula alpha := InternalClosedPrograms.allBlock (matrix E elapsed)
end Induction

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryFiniteDescent.InductionDefinitions
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryFiniteDescent.InductionDefinitions
