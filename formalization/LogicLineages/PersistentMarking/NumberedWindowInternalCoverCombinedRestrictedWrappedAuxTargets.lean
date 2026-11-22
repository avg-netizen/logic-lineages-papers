module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedWrapperTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedWrappedAuxTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc z)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary rawCons)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSettingsGrammarGuardDefinitions (refitGuard)
open NumberedWindowInternalCoverCombinedRestrictedTargets (combinedPrograms)
open NumberedWindowInternalCoverCombinedRestrictedWrapperTargets (thinMatchingWindow thinContextPresent)

structure ActualThinWindowInputs (C baseW : Program 3) (V : Program 1) (s : Settings)
    (body : Positive (Fin 1)) {α : Type} (Γ : List (Formula α)) (ctx ty raw : OTerm α) : Prop where
  valid : Nonempty (Derivation body Γ (unary V (suc z) raw))
  typed : Nonempty (Derivation body Γ (windowAt baseW ctx ty raw))
  context : Nonempty (Derivation body Γ (windowAt thinContextPresent ctx ty raw))

def ExactOpenCoverThinMatchingWindowInputs : Prop :=
  ∀ (C baseW : Program 3) (V : Program 1) (s : Settings)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (ctx ty raw : OTerm α),
    Nonempty (Derivation body Γ (windowAt (thinMatchingWindow C s baseW V) ctx ty raw)) →
    ActualThinWindowInputs C baseW V s body Γ ctx ty raw

/-- Changing other tape coordinates does not change the actual parser
input. Neither a different context nor a numeric parser is admitted. -/
def ExactOpenCoverThinMatchingContextTransport : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (ctx oldTy oldRaw newTy newRaw : OTerm α),
    Nonempty (Derivation body Γ (windowAt thinContextPresent ctx oldTy oldRaw)) →
    Nonempty (Derivation body Γ (windowAt thinContextPresent ctx newTy newRaw))

/-- Actual wrapped auxiliary formation with the unchanged combined
P, and independently supplied bits from its two different type guards. -/
def ExactOpenCoverCombinedWrappedAuxFormation : Prop :=
  ∀ (V TV M M0 : Program 1) (B : Program 2) (T : Program 1) (s : Settings)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (ctx dom cod fn arg : OTerm α),
    let P := combinedPrograms s V TV M M0 B T
    let W := thinMatchingWindow P.cover s P.W P.V
    Nonempty (Derivation body Γ (unary TV (suc z) dom ⊓ unary TV (suc z) cod)) →
    Nonempty (Derivation body Γ (unary (refitGuard s T) (suc z) dom ⊓ unary (refitGuard s T) (suc z) cod)) →
    Nonempty (Derivation body Γ (windowAt W ctx (rawCons dom cod) fn)) →
    Nonempty (Derivation body Γ (windowAt W ctx dom arg)) →
    Nonempty (Derivation body Γ (windowAt W ctx cod (auxiliaryTerm dom cod fn arg)))

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedWrappedAuxTargets
