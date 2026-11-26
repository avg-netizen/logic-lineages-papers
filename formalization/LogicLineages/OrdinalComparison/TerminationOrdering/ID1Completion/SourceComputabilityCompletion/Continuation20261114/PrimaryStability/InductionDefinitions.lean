module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryStability.InclusionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryStability.InductionDefinitions
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
def result {alpha : Type} (initial out : OTerm alpha) : Formula alpha := PrimaryMonotonicity.included out initial
def fields {alpha : Type} (E : Program 3) (count pool initial first parameter out : OTerm alpha) : Formula alpha :=
  graph3 (PrimaryExpansion.expand E) first pool initial parameter ⊓
    (PrimaryMonotonicity.included first initial ⊓ graph4 (PrimaryIteration.iterate E) out count pool initial parameter)
def matrix {alpha : Type} (E : Program 3) (count : OTerm alpha) : Formula (alpha ⊕ Fin 5) :=
  (fields E (count.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2))
    (.var (.inr 3)) (.var (.inr 4))).imp (result (.var (.inr 1)) (.var (.inr 4)))
def AtCount {alpha : Type} (E : Program 3) (count : OTerm alpha) : Formula alpha := InternalClosedPrograms.allBlock (matrix E count)
end Induction

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryStability.InductionDefinitions
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryStability.InductionDefinitions
