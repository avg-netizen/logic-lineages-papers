module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverOrdinaryMeasureTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedTypeWindowTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (branch constantZero)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc)
open LogicLineages.ComputabilityKnowledge GorbowPRProgram GorbowVerifierNormalization
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelope (field)
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
open NumberedWindowInternalCoverNumberedLayerTargets (numberedTerm)
open NumberedWindowInternalCoverHeadWindowTargets (grammarHeadBase headFittedWindow headPrior)
open NumberedWindowInternalCoverFittedInductionDispatchTargets (fittedWindowBase)
open NumberedWindowInternalCoverOrdinaryMeasureTargets (ordinaryPrograms)
open NumberedWindowInternalCoverRefinedInductionDispatchTargets (Programs)

/-- Stored numbered annotation is original field 1, not the head or id. -/
def numberedGrammarType (s : Settings) : Program 1 :=
  .composition (grammarTypeAt s) (fun _ : Fin 1 => field 1)

def numberedTypeGuard (s : Settings) (B : Program 2) : Program 2 :=
  branch (normalize (onRaw (numberedGrammarType s))) (constantZero 2) B

def numberedTypeBase (s : Settings) (B : Program 2) : Program 2 :=
  branch (onRaw (header 5 5)) B (numberedTypeGuard s B)

abbrev numberedTypeWindow (s : Settings) (B : Program 2) (T : Program 1) : Program 3 :=
  headFittedWindow s (numberedTypeBase s B) T

abbrev numberedTypePrograms (s : Settings) (V TV M A : Program 1) (B : Program 2) (T : Program 1) : Programs :=
  ordinaryPrograms s V TV M A (numberedTypeBase s B) T

abbrev numberedTypePrior {α : Type} (h ty k l r : OTerm α) : OTerm α :=
  headPrior true h [ty,k,l,r]

def ExactCoverNumberedTypeBase : Prop :=
  ∀ (s : Settings) (B : Program 2), GrammarTypeInclusion s → IntrinsicWindowCalibrated s B →
    IntrinsicWindowCalibrated s (numberedTypeBase s B)

def ExactCoverNumberedTypeWindowCalibrated : Prop :=
  ∀ (s : Settings) (B : Program 2) (T : Program 1), GrammarTypeInclusion s →
    IntrinsicWindowCalibrated s B → TypeGuardCalibrated s T → ActualPackedWindow s (numberedTypeWindow s B T)

def ExactOpenCoverNumberedTypeIntrinsic : Prop :=
  ∀ (s : Settings) (B : Program 2) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (ctx h ty k l r result : OTerm α),
    Nonempty (Derivation body Γ (programGraph
      (fittedWindowBase s (grammarHeadBase s (numberedTypeBase s B))) (suc result)
      ![ctx,numberedTerm h ty k l r])) →
    Nonempty (Derivation body Γ (memberGraph (typesTerm s α) ty))

def ExactOpenCoverNumberedTypeWindow : Prop :=
  ∀ (s : Settings) (B : Program 2) (T : Program 1) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (ctx h ty k l r result : OTerm α),
    Nonempty (Derivation body Γ (windowGraph (numberedTypeWindow s B T) ctx result (numberedTerm h ty k l r))) →
    Nonempty (Derivation body Γ (memberGraph (typesTerm s α) ty))

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedTypeWindowTargets
