module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentGrammarInductionTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentGrammarInductionExistentialProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentGrammarInductionBindingProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedMemoZeroProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWidthObservationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarNullaryEmptyArgsProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendTransitionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentGrammarInductionSeedProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (z zRelabel)
open ID1Completion.InternalApplicationValidityStackAppendTransitionProof (pairZero)
open ID1Completion.GuardedSourceSyntaxProof (numeralRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalFactoredAuxOwnCoverTargets (headsTerm typesTerm)
open NumberedWindowInternalCoverSelectedMemoZeroProof (exact_OpenCoverSelectedMemoZero)
open NumberedWindowInternalCoverSelectedGrammarWidthObservationProof (observationCases)
open NumberedWindowInternalCoverSelectedGrammarNullaryEmptyArgsProof (exact_OpenSelectedGrammarEmptyArgs)
open NumberedWindowInternalCoverArgumentMemoTargets (argumentUpdate)
open NumberedWindowInternalCoverArgumentGrammarInductionBindingProof (argumentExistsRename)
open NumberedWindowInternalCoverArgumentGrammarInductionExistentialProof (introduceArgument)
open NumberedWindowInternalCoverArgumentGrammarInductionTargets

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem actualArgumentGrammarSeed (F : Program 1) (s : Settings) :
    Nonempty (Derivation body Γ (argumentExists F s (z : OTerm α))) := by
  apply observationCases z (headsTerm s α) (typesTerm s α) z (argumentExists F s z)
  intro β j Δ state terms args _ actual
  simp only [argumentExistsRename,zRelabel]
  simp only [headsTerm,typesTerm,numeralRename,zRelabel] at actual
  have hit := exact_OpenSelectedGrammarEmptyArgs body β Δ z (headsTerm s β) (typesTerm s β)
    z state terms args actual
  exact introduceArgument F s z z z z state terms args
    (exact_OpenCoverSelectedMemoZero (argumentUpdate F) body β Δ) pairZero ⟨actual,hit⟩

#print axioms actualArgumentGrammarSeed

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentGrammarInductionSeedProof
