module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryMonotonicity.InclusionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryMonotonicity.InductionDefinitions
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open SourceComputabilityFormulaSupportProof InternalControlGraphSupportProof
open InternalRecursionGraphStepSyntaxProof InternalTagArithmeticSyntaxProof
open InternalRawListRecursionSyntaxProof InternalGraphCompositionSyntaxProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalAdditionLawsProof InternalGraphCompositionFunctionalityProof
open InternalApplicationCertificateConstructorsSupportProof InternalAcceptanceSupportProof
open InternalApplicationStepPeelSupportProof (andIntro)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InternalClosedPrograms InternalClosedProgramsBindingProof
open TwoSol20261113.CalibratedPrimary.Membership
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

def fields {alpha : Type} (E : Program 3)
    (count pool left right parameter leftOut rightOut : OrdinaryArithmetic.Term alpha) : Formula alpha :=
  included left right ⊓
    (graph4 (PrimaryIteration.iterate E) leftOut count pool left parameter ⊓
     graph4 (PrimaryIteration.iterate E) rightOut count pool right parameter)
def matrix {alpha : Type} (E : Program 3) (count : OrdinaryArithmetic.Term alpha) : Formula (alpha ⊕ Fin 6) :=
  (fields E (count.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2))
    (.var (.inr 3)) (.var (.inr 4)) (.var (.inr 5))).imp
      (included (.var (.inr 4)) (.var (.inr 5)))
def AtCount {alpha : Type} (E : Program 3) (count : OrdinaryArithmetic.Term alpha) : Formula alpha :=
  allBlock (matrix E count)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryMonotonicity.InductionDefinitions
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryMonotonicity.InductionDefinitions
