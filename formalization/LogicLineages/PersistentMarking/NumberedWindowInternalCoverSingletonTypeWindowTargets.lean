module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSingletonTypeArgumentTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSingletonTypeWindowTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (branch conjunction constantZero)
open LogicLineages.ComputabilityKnowledge GorbowPRProgram GorbowVerifierNormalization
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelope (applyUnary field)
open NumberedWindowInternalSparseFieldCell (cellHead)
open NumberedWindowInternalCoverTypeLeafIntrinsicTargets (onRaw)
open NumberedWindowInternalCoverSelectedValidityTargets (header)
open NumberedWindowInternalSettingsGrammarGuardDefinitions (grammarTypeAt)
open NumberedWindowInternalSettingsGrammarGuardNumericTargets (GrammarTypeInclusion)
open NumberedWindowInternalAuxWindowMemoTargets (IntrinsicWindowCalibrated)
open NumberedWindowInternalAuxWindowStepTargets (TypeGuardCalibrated)
open NumberedWindowInternalAuxWindowOpenTargets (windowGraph)
open NumberedWindowInternalSparseTypedRawTargets (ActualPackedWindow)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalFactoredAuxOwnCoverTargets (typesTerm)
open NumberedWindowInternalCoverSelectedGrammarOrdinaryOwnTargets (ordinaryKey)
open NumberedWindowInternalCoverLambdaLexicalWindowTargets (lambdaLexicalWindow)
open NumberedWindowInternalCoverRefinedInductionDispatchTargets (ParentRow)
open NumberedWindowInternalCoverLambdaBoundCoherenceTargets (lexicalFittedPrograms)
open NumberedWindowInternalCoverSingletonTypeArgumentTargets (singletonTypeGuard singletonTypeArgs singletonTypeKey)

def ordinarySingletonGuard : Program 1 :=
  conjunction (header 4 2) (applyUnary singletonTypeGuard (field 1))

def singletonTypeSelector : Program 1 := applyUnary (field 0) (applyUnary cellHead (field 1))

def singletonArgumentTypeAt (s : Settings) : Program 1 :=
  applyUnary (grammarTypeAt s) singletonTypeSelector

def ordinarySingletonKBranch (s : Settings) (B : Program 2) : Program 2 :=
  branch (normalize (onRaw (singletonArgumentTypeAt s))) (constantZero 2) B

/-- Never change a nonmatching key; on matching keys use the physically
validated original K and retain the original B output if admitted. -/
def ordinarySingletonKBase (s : Settings) (B : Program 2) : Program 2 :=
  branch (onRaw ordinarySingletonGuard) B (ordinarySingletonKBranch s B)

abbrev ordinarySingletonKWindow (s : Settings) (B : Program 2) (T : Program 1) :=
  lambdaLexicalWindow s (ordinarySingletonKBase s B) T

def ExactCoverOrdinarySingletonKBase : Prop :=
  ∀ (s : Settings) (B : Program 2), GrammarTypeInclusion s → IntrinsicWindowCalibrated s B →
    IntrinsicWindowCalibrated s (ordinarySingletonKBase s B)

def ExactCoverOrdinarySingletonKWindowCalibrated : Prop :=
  ∀ (s : Settings) (B : Program 2) (T : Program 1), GrammarTypeInclusion s →
    IntrinsicWindowCalibrated s B → TypeGuardCalibrated s T →
    ActualPackedWindow s (ordinarySingletonKWindow s B T)

def ExactOpenCoverOrdinarySingletonKWindow : Prop :=
  ∀ (s : Settings) (B : Program 2) (T : Program 1) (body : Positive (Fin 1)) (α : Type)
    (Γ : List (Formula α)) (ctx h ty result : OTerm α),
    Nonempty (Derivation body Γ (windowGraph (ordinarySingletonKWindow s B T)
      ctx result (ordinaryKey h (singletonTypeKey ty)))) →
    Nonempty (Derivation body Γ (memberGraph (typesTerm s α) ty))

def ExactOpenCoverOrdinarySingletonKScratch : Prop :=
  ∀ (V TV M A : Program 1) (B : Program 2) (T : Program 1) (s : Settings)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (h ty p vertices ctx result : OTerm α),
    ParentRow (lexicalFittedPrograms s V TV M (singletonTypeArgs A) (ordinarySingletonKBase s B) T)
      s body Γ (ordinaryKey h (singletonTypeKey ty)) p vertices ctx result →
    Nonempty (Derivation body Γ (memberGraph vertices (ordinaryKey h (singletonTypeKey ty))))

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSingletonTypeWindowTargets
