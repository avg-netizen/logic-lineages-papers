module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedEmptyTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedMeasureSelectedCutProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedMeasureSelectedArgsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedMeasureCombineOpenProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendTransitionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedEmptyMeasureProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (z)
open ID1Completion.InternalApplicationValidityStackAppendTransitionProof (pairZero notLessZero)
open ID1Completion.InternalLessThanSupportProof (rejectOfNotLess)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchIntro)
open ID1Completion.InternalAcceptanceConjunctionProof (constantZeroValue)
open ID1Completion.InternalControlGraphSupportProof (projectionValue)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalChosenAuxMeasureCombine (maximum)
open NumberedWindowInternalCoverOrdinaryMeasureTargets (selectedArgsMeasure)
open NumberedWindowInternalCoverNumberedMeasureCombineOpenProof (exact_OpenCoverNumberedJoin)
open NumberedWindowInternalCoverNumberedMeasureSelectedCutProof (exact_OpenCoverNumberedMeasureCut)
open NumberedWindowInternalCoverNumberedMeasureSelectedArgsProof (exact_OpenNumberedJoinFromFields)
open NumberedWindowInternalCoverNumberedEmptyTargets

private theorem maxAtZero {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)} (n : OTerm α) :
    Nonempty (Derivation body Γ (programGraph maximum n ![n,z])) :=
  zeroBranchIntro ID1Completion.InternalLessThan.ltTest (.projection 0) (.projection 1)
    n ![n,z] (rejectOfNotLess n z (notLessZero n)) (projectionValue 0 ![n,z])

theorem exact_OpenCoverNumberedEmptyMeasure : ExactOpenCoverNumberedEmptyMeasure := by
  intro M A body α Γ h ty k p actual
  have zeroArg : Nonempty (Derivation body Γ (unary (selectedArgsMeasure A) z (z : OTerm α))) :=
    zeroBranchIntro (.projection 0) (constantZero 1) A z ![z] (projectionValue 0 ![z]) (constantZeroValue ![z])
  have cut := exact_OpenCoverNumberedMeasureCut M A body α Γ h ty k z z p actual
  have join := exact_OpenNumberedJoinFromFields A h ty k z z p z z cut zeroArg zeroArg
  exact exact_OpenCoverNumberedJoin body α Γ p k z z z z z z z k
    pairZero pairZero (maxAtZero z) (maxAtZero k) join

#print axioms exact_OpenCoverNumberedEmptyMeasure

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedEmptyMeasureProof
