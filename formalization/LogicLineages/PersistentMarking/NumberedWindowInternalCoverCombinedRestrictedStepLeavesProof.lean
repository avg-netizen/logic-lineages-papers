module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedStepTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeafSharedMeasureProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverTypeLeafSharedMeasureProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeafGrammarWindowProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverTypeLeafStrictWindowProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarNamedLeafScratchProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarTypeLeafScratchProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverFittedInductionDispatchAuxTypesProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverRefinedOwnEarlierProof
import LogicLineages.PersistentMarking.NumberedWindowInternalStrictAuxWindowResultTypeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverRefinedInductionDispatchTransportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedStepLeavesProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (z)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalAuxMeasureMemoTargets (selectedMeasure)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalCoverNamedLeavesTargets (namedTerm)
open NumberedWindowInternalCoverTypeLeavesTargets (typeLeafTerm)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalCoverNamedLeafMeasureTargets (namedMeasureBase namedSharedMeasure)
open NumberedWindowInternalCoverArgumentMemoTargets (argumentMeasure)
open NumberedWindowInternalCoverOrdinaryMeasureTargets (ordinaryMeasureBase)
open NumberedWindowInternalCoverNumberedMeasureSelectedTargets (numberedMeasureBase)
open NumberedWindowInternalCoverFittedInductionDispatchTargets (fittedMeasureBase fittedWindowBase)
open NumberedWindowInternalCoverNumberedTypeWindowTargets (numberedTypeBase)
open NumberedWindowInternalCoverHeadWindowTargets (grammarHeadBase)
open NumberedWindowInternalCoverLambdaLexicalWindowTargets (lambdaLexicalBase)
open NumberedWindowInternalCoverNamedLeafIntrinsicTargets (namedGrammarBase)
open NumberedWindowInternalCoverLexicalBoundWindowTargets (lexicalBoundBase)
open NumberedWindowInternalCoverNamedResultTargets (namedResultBase)
open NumberedWindowInternalSettingsGrammarGuardDefinitions (refitGuard)
open NumberedWindowInternalCoverNamedLeafSharedMeasureProof (exact_OpenCoverNamedLeafSharedMeasure)
open NumberedWindowInternalCoverTypeLeafSharedMeasureProof (exact_OpenCoverTypeLeafSharedMeasure)
open NumberedWindowInternalCoverNamedLeafGrammarWindowProof (exact_OpenCoverNamedLeafGrammarWindowK)
open NumberedWindowInternalCoverTypeLeafStrictWindowProof (exact_OpenCoverTypeLeafStrictWindowK)
open NumberedWindowInternalCoverSelectedGrammarNamedLeafScratchProof (exact_OpenSelectedGrammarNamedLeafScratch)
open NumberedWindowInternalCoverSelectedGrammarTypeLeafScratchProof (exact_OpenSelectedGrammarTypeLeafScratch)
open NumberedWindowInternalCoverFittedInductionDispatchAuxTypesProof (exact_OpenFittedAuxTypes)
open NumberedWindowInternalStrictAuxWindowResultTypeProof (exact_OpenStrictAuxWindowResultType)
open NumberedWindowInternalCoverRefinedInductionDispatchTransportProof (moveWindowType)
open NumberedWindowInternalCoverRefinedOwnEarlierProof (exact_OpenCoverRefinedAuxOwnEarlier)
open NumberedWindowInternalCoverRefinedInductionDispatchTargets (ParentRow PackedRow)
open NumberedWindowInternalCoverCombinedRestrictedTargets

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private abbrev measureCore (M M0 : Program 1) : Program 1 :=
  let A := argumentMeasure (namedSharedMeasure M0)
  ordinaryMeasureBase (numberedMeasureBase M A) A

private abbrev windowCore (s : Settings) (B : Program 2) (T : Program 1) : Program 2 :=
  grammarHeadBase s (numberedTypeBase s (lambdaLexicalBase s (combinedCallback s B) T))

theorem combinedAtNamed (s : Settings) (V TV M M0 : Program 1) (B : Program 2) (T : Program 1)
    (b : Bool) (p vertices ctx result ty i : OTerm α)
    (row : ParentRow (combinedPrograms s V TV M M0 B T) s body Γ
      (namedTerm b.toNat ty i) p vertices ctx result) :
    Nonempty (Derivation body Γ (memberGraph vertices (namedTerm b.toNat ty i))) := by
  let P := combinedPrograms s V TV M M0 B T
  let C := measureCore M M0
  let D := windowCore s B T
  have bounds := exact_OpenCoverNamedLeafSharedMeasure b C body α Γ ty i p row.parent.measured
  have actualK := exact_OpenCoverNamedLeafGrammarWindowK b s (lexicalBoundBase (namedResultBase D))
    (refitGuard s T) body α Γ ctx ty i result row.typed
  exact exact_OpenSelectedGrammarNamedLeafScratch b P.V (selectedMeasure P.R) s body α Γ
    p z i vertices ty i actualK bounds.2 row.parent.valid row.parent.measured bounds.1 row.parent.held

theorem combinedAtType (s : Settings) (V TV M M0 : Program 1) (B : Program 2) (T : Program 1)
    (p vertices ctx result ty : OTerm α)
    (row : ParentRow (combinedPrograms s V TV M M0 B T) s body Γ (typeLeafTerm ty) p vertices ctx result) :
    Nonempty (Derivation body Γ (memberGraph vertices (typeLeafTerm ty))) := by
  let P := combinedPrograms s V TV M M0 B T
  let C := measureCore M M0
  let D := windowCore s B T
  have pair := exact_OpenCoverTypeLeafSharedMeasure (namedMeasureBase C) body α Γ ty p row.parent.measured
  have actualK := exact_OpenCoverTypeLeafStrictWindowK s (namedGrammarBase s (lexicalBoundBase (namedResultBase D)))
    (refitGuard s T) body α Γ ctx ty result row.typed
  exact exact_OpenSelectedGrammarTypeLeafScratch P.V (selectedMeasure P.R) s body α Γ
    p z z vertices ty actualK row.parent.valid row.parent.measured pair row.parent.held

theorem combinedAtAux (s : Settings) (V TV M M0 : Program 1) (B : Program 2) (T : Program 1)
    (raw p vertices ctx result dom cod fn arg : OTerm α)
    (row : PackedRow (combinedPrograms s V TV M M0 B T) s body Γ raw (auxiliaryTerm dom cod fn arg)
      p vertices ctx result 6 [dom,cod,fn,arg]) :
    Nonempty (Derivation body Γ (memberGraph vertices (auxiliaryTerm dom cod fn arg))) := by
  let P := combinedPrograms s V TV M M0 B T
  let C := measureCore M M0
  let D := windowCore s B T
  let A := fittedWindowBase s D
  let S := refitGuard s T
  let key := auxiliaryTerm dom cod fn arg
  have actualK := exact_OpenFittedAuxTypes V TV C D T s raw p vertices ctx result dom cod fn arg row
  obtain ⟨actualType⟩ := exact_OpenStrictAuxWindowResultType A S body α Γ ctx result dom cod fn arg row.data.typed
  have typed := moveWindowType P.W ctx result cod key actualType row.data.typed
  exact exact_OpenCoverRefinedAuxOwnEarlier V TV (fittedMeasureBase C) A S s body α Γ
    p vertices ctx dom cod fn arg row.data.parent row.data.branchBelow typed actualK.1 actualK.2

#print axioms combinedAtNamed
#print axioms combinedAtType
#print axioms combinedAtAux

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedStepLeavesProof
