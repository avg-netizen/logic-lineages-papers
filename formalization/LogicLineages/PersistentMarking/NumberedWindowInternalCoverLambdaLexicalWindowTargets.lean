module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaLexicalSourceTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaLexicalWindowTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (branch constantZero)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc eqn)
open LogicLineages.ComputabilityKnowledge GorbowPRProgram GorbowVerifierNormalization
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelope (field)
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons)
open NumberedWindowInternalSparsePair (fieldCons)
open NumberedWindowInternalCoverAuxApplicationsTargets (binary)
open NumberedWindowInternalChosenAuxMeasureCombine (callOne)
open NumberedWindowInternalCoverTypeLeafIntrinsicTargets (onRaw leafTypeTest)
open NumberedWindowInternalCoverLambdaLayerTargets (lambdaTerm)
open NumberedWindowInternalCoverSelectedValidityTargets (header)
open NumberedWindowInternalCoverNumberedTypeWindowTargets (numberedTypeBase numberedTypeWindow)
open NumberedWindowInternalCoverHeadWindowTargets (grammarHeadBase)
open NumberedWindowInternalCoverFittedInductionDispatchTargets (fittedWindowBase)
open NumberedWindowInternalSettingsGrammarGuardDefinitions (refitGuard)
open NumberedWindowInternalSettingsGrammarGuardNumericTargets (GrammarTypeInclusion)
open NumberedWindowInternalAuxWindowMemoTargets (IntrinsicWindowCalibrated)
open NumberedWindowInternalAuxWindowStepTargets (TypeGuardCalibrated)
open NumberedWindowInternalStrictAuxWindowTargets (strictAuxIntrinsic)
open NumberedWindowInternalAuxWindowOpenTargets (windowGraph)
open NumberedWindowInternalSparseTypedRawTargets (ActualPackedWindow)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalFactoredAuxOwnCoverTargets (typesTerm)

abbrev precedingBase (s : Settings) (B : Program 2) : Program 2 :=
  fittedWindowBase s (grammarHeadBase s (numberedTypeBase s B))

/-- This is the previously fixed actual selected intrinsic, not a proposed
numerical reflection of arbitrary window graphs and not the new window. -/
abbrev precedingIntrinsic (s : Settings) (B : Program 2) (T : Program 1) : Program 2 :=
  strictAuxIntrinsic (precedingBase s B) (refitGuard s T)

def lambdaLexicalPush : Program 2 :=
  binary fieldCons (onRaw (field 0)) (.projection 0)

def lambdaOldBody (s : Settings) (B : Program 2) (T : Program 1) : Program 2 :=
  binary (precedingIntrinsic s B T) lambdaLexicalPush (onRaw (field 1))

def lambdaArrowCode (s : Settings) (B : Program 2) (T : Program 1) : Program 2 :=
  binary fieldCons (onRaw (field 0))
    (callOne ID1Completion.InternalEqualityTest.predecessor (lambdaOldBody s B T))

def lambdaLexicalResult (s : Settings) (B : Program 2) (T : Program 1) : Program 2 :=
  callOne .succ (lambdaArrowCode s B T)

def lambdaCheckedBody (s : Settings) (B : Program 2) (T : Program 1) : Program 2 :=
  branch (lambdaOldBody s B T) (constantZero 2) (lambdaLexicalResult s B T)

def lambdaCheckedDomain (s : Settings) (B : Program 2) (T : Program 1) : Program 2 :=
  branch (normalize (onRaw (leafTypeTest s))) (constantZero 2) (lambdaCheckedBody s B T)

def lambdaPositive (s : Settings) (B : Program 2) (T : Program 1) : Program 2 :=
  branch B (constantZero 2) (lambdaCheckedDomain s B T)

def lambdaLexicalBase (s : Settings) (B : Program 2) (T : Program 1) : Program 2 :=
  branch (onRaw (header 2 2)) B (lambdaPositive s B T)

abbrev lambdaLexicalWindow (s : Settings) (B : Program 2) (T : Program 1) : Program 3 :=
  numberedTypeWindow s (lambdaLexicalBase s B T) T

def ExactCoverLambdaPrecedingIntrinsic : Prop :=
  ∀ (s : Settings) (B : Program 2) (T : Program 1), GrammarTypeInclusion s →
    IntrinsicWindowCalibrated s B → TypeGuardCalibrated s T →
    IntrinsicWindowCalibrated s (precedingIntrinsic s B T)

def ExactCoverLambdaLexicalBase : Prop :=
  ∀ (s : Settings) (B : Program 2) (T : Program 1), GrammarTypeInclusion s →
    IntrinsicWindowCalibrated s B → TypeGuardCalibrated s T →
    IntrinsicWindowCalibrated s (lambdaLexicalBase s B T)

def ExactCoverLambdaLexicalWindow : Prop :=
  ∀ (s : Settings) (B : Program 2) (T : Program 1), GrammarTypeInclusion s →
    IntrinsicWindowCalibrated s B → TypeGuardCalibrated s T →
    ActualPackedWindow s (lambdaLexicalWindow s B T)

structure ActualPrecedingLambdaChild (s : Settings) (B : Program 2) (T : Program 1)
    (body : Positive (Fin 1)) {α : Type} (Γ : List (Formula α))
    (ctx ty q result childTy : OTerm α) : Prop where
  pastWindow : Nonempty (Derivation body Γ (windowGraph (numberedTypeWindow s B T) (rawCons ty ctx) childTy q))
  domain : Nonempty (Derivation body Γ (memberGraph (typesTerm s α) ty))
  resultArrow : Nonempty (Derivation body Γ (eqn result (rawCons ty childTy)))

def ExactOpenCoverLambdaLexicalWindow : Prop :=
  ∀ (s : Settings) (B : Program 2) (T : Program 1) (body : Positive (Fin 1)) (α : Type)
    (Γ : List (Formula α)) (ctx ty q result : OTerm α) (Q : Formula α),
    Nonempty (Derivation body Γ (windowGraph (lambdaLexicalWindow s B T) ctx result (lambdaTerm ty q))) →
    (∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (childTy : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      ActualPrecedingLambdaChild s B T body Δ (ctx.relabel j) (ty.relabel j) (q.relabel j)
        (result.relabel j) childTy →
      Nonempty (Derivation body Δ (Q.relabel j))) →
    Nonempty (Derivation body Γ Q)

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaLexicalWindowTargets
