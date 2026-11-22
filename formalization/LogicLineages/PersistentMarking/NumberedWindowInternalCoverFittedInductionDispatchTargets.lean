module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverRefinedInductionDispatchTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedResultTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSettingsGrammarGuardNumericTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverFittedInductionDispatchTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalCoverLambdaLayerTargets (lambdaTerm)
open NumberedWindowInternalCoverNumberedLayerTargets (numberedTerm)
open NumberedWindowInternalCoverSelectedGrammarOrdinaryOwnTargets (ordinaryKey)
open NumberedWindowInternalCoverTypeLeafMeasureTargets (leafMeasureBase)
open NumberedWindowInternalCoverNamedLeafMeasureTargets (namedMeasureBase)
open NumberedWindowInternalCoverTypeLeafIntrinsicTargets (leafIntrinsicBase)
open NumberedWindowInternalCoverNamedLeafIntrinsicTargets (namedGrammarBase)
open NumberedWindowInternalCoverLexicalBoundWindowTargets (lexicalBoundBase)
open NumberedWindowInternalCoverNamedResultTargets (namedResultBase)
open NumberedWindowInternalSettingsGrammarGuardDefinitions (refitGuard)
open NumberedWindowInternalSettingsGrammarGuardNumericTargets (GrammarTypeInclusion)
open NumberedWindowInternalCoverRefinedInductionDispatchTargets
open NumberedWindowInternalAuxExchangeMemoStepTargets (TermSyntaxCalibrated)
open NumberedWindowInternalCoverLambdaSyntaxRowTargets (TypeSyntaxCalibrated)
open NumberedWindowInternalFactoredCoverTargets (TermMeasureCalibrated)
open NumberedWindowInternalAuxWindowMemoTargets (IntrinsicWindowCalibrated)
open NumberedWindowInternalAuxWindowStepTargets (TypeGuardCalibrated)
open NumberedWindowInternalAuxMeasureMemoTargets (selectedMeasure)
open NumberedWindowInternalSparseTypedRawTargets (ActualPackedWindow)

/-- One exact common program combination. In particular the original
unary V callback and its type-syntax-only TV are not replaced by TW. -/
abbrev fittedMeasureBase (M : Program 1) : Program 1 := leafMeasureBase (namedMeasureBase M)

abbrev fittedWindowBase (s : Settings) (B : Program 2) : Program 2 :=
  leafIntrinsicBase s (namedGrammarBase s (lexicalBoundBase (namedResultBase B)))

abbrev fittedPrograms (s : Settings) (V TV M : Program 1) (B : Program 2) (TW : Program 1) : Programs :=
  refinedPrograms V TV (fittedMeasureBase M) (fittedWindowBase s B) (refitGuard s TW)

/-- No extra obligations at tags 0, 1, 3, or 6. All unpaid facts are
supplied on exactly the genuine packed parent and its original context. -/
structure Remaining (P : Programs) (s : Settings) (body : Positive (Fin 1)) : Prop where
  lambdaBody : ∀ (α : Type) (Γ : List (Formula α)) (raw p vertices ctx result ty q : OTerm α)
    (goal : Formula α),
    PackedRow P s body Γ raw (lambdaTerm ty q) p vertices ctx result 2 [ty,q] →
    Supplies body Γ goal (fun β j Δ => LambdaFacts P.W s body Δ
      (ctx.relabel j) (result.relabel j) (ty.relabel j) (q.relabel j))
  ordinary : ∀ (α : Type) (Γ : List (Formula α)) (raw p vertices ctx result h a : OTerm α)
    (goal : Formula α),
    PackedRow P s body Γ raw (ordinaryKey h a) p vertices ctx result 4 [h,a] →
    Supplies body Γ goal (fun β j Δ => OrdinaryFacts s body Δ (p.relabel j) (h.relabel j) (a.relabel j))
  numbered : ∀ (α : Type) (Γ : List (Formula α)) (raw p vertices ctx result h ty k l r : OTerm α)
    (goal : Formula α),
    PackedRow P s body Γ raw (numberedTerm h ty k l r) p vertices ctx result 5 [h,ty,k,l,r] →
    Supplies body Γ goal (fun β j Δ => NumberedFacts s body Δ (p.relabel j)
      (h.relabel j) (ty.relabel j) (k.relabel j) (l.relabel j) (r.relabel j))

def ExactCoverFittedInductionPrograms : Prop :=
  ∀ (s : Settings) (V TV M : Program 1) (B : Program 2) (TW : Program 1),
    GrammarTypeInclusion s → TermSyntaxCalibrated V → TypeSyntaxCalibrated TV →
    TermMeasureCalibrated M → IntrinsicWindowCalibrated s B → TypeGuardCalibrated s TW →
    let P := fittedPrograms s V TV M B TW
    TermSyntaxCalibrated P.V ∧ TermMeasureCalibrated (selectedMeasure P.R) ∧ ActualPackedWindow s P.W

def ExactOpenCoverFittedInductionDispatch : Prop :=
  ∀ (V TV M : Program 1) (B : Program 2) (TW : Program 1) (s : Settings)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (raw p vertices ctx result : OTerm α),
    let P := fittedPrograms s V TV M B TW
    Remaining P s body →
    ParentRow P s body Γ raw p vertices ctx result →
    Nonempty (Derivation body Γ (memberGraph vertices raw))

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverFittedInductionDispatchTargets
