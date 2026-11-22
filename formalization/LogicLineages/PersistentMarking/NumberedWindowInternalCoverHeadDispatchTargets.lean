module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverHeadWindowTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverHeadDispatchTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalFactoredAuxOwnCoverTargets (headsTerm typesTerm measurePair)
open NumberedWindowInternalCoverSelectedGrammarNumberedOwnTargets (BoundedNumberedArgs)
open NumberedWindowInternalCoverLambdaLayerTargets (lambdaTerm)
open NumberedWindowInternalCoverSelectedGrammarOrdinaryOwnTargets (ordinaryKey)
open NumberedWindowInternalCoverNumberedLayerTargets (numberedTerm)
open NumberedWindowInternalCoverRefinedInductionDispatchTargets
open NumberedWindowInternalCoverFittedInductionDispatchTargets (fittedPrograms)
open NumberedWindowInternalCoverHeadWindowTargets (grammarHeadBase headFittedWindow)
open NumberedWindowInternalSettingsGrammarGuardNumericTargets (GrammarTypeInclusion)
open NumberedWindowInternalAuxWindowMemoTargets (IntrinsicWindowCalibrated)
open NumberedWindowInternalAuxWindowStepTargets (TypeGuardCalibrated)
open NumberedWindowInternalSparseTypedRawTargets (ActualPackedWindow)

abbrev headPrograms (s : Settings) (V TV M : Program 1) (B : Program 2) (T : Program 1) : Programs :=
  fittedPrograms s V TV M (grammarHeadBase s B) T

def OrdinaryNoHeadFacts (s : Settings) (body : Positive (Fin 1)) {α : Type} (Γ : List (Formula α))
    (p a : OTerm α) : Prop :=
  ∃ d width da wa state terms args : OTerm α,
    Nonempty (Derivation body Γ (measurePair p d width)) ∧
    BoundedNumberedArgs body Γ d (headsTerm s α) (typesTerm s α) width da wa state terms args a

def NumberedNoHeadFacts (s : Settings) (body : Positive (Fin 1)) {α : Type} (Γ : List (Formula α))
    (p ty k l r : OTerm α) : Prop :=
  ∃ d width dl wl ls lt la dr wr rs rt ra : OTerm α,
    Nonempty (Derivation body Γ (measurePair p d width)) ∧
    BoundedNumberedArgs body Γ d (headsTerm s α) (typesTerm s α) width dl wl ls lt la l ∧
    BoundedNumberedArgs body Γ d (headsTerm s α) (typesTerm s α) width dr wr rs rt ra r ∧
    Nonempty (Derivation body Γ (memberGraph (typesTerm s α) ty)) ∧
    Nonempty (Derivation body Γ (ltF k (suc width)))

structure RemainingWithoutHeads (P : Programs) (s : Settings) (body : Positive (Fin 1)) : Prop where
  lambdaBody : ∀ (α : Type) (Γ : List (Formula α)) (raw p vertices ctx result ty q : OTerm α)
    (goal : Formula α),
    PackedRow P s body Γ raw (lambdaTerm ty q) p vertices ctx result 2 [ty,q] →
    Supplies body Γ goal (fun β j Δ => LambdaFacts P.W s body Δ
      (ctx.relabel j) (result.relabel j) (ty.relabel j) (q.relabel j))
  ordinary : ∀ (α : Type) (Γ : List (Formula α)) (raw p vertices ctx result h a : OTerm α)
    (goal : Formula α),
    PackedRow P s body Γ raw (ordinaryKey h a) p vertices ctx result 4 [h,a] →
    Supplies body Γ goal (fun β j Δ => OrdinaryNoHeadFacts s body Δ (p.relabel j) (a.relabel j))
  numbered : ∀ (α : Type) (Γ : List (Formula α)) (raw p vertices ctx result h ty k l r : OTerm α)
    (goal : Formula α),
    PackedRow P s body Γ raw (numberedTerm h ty k l r) p vertices ctx result 5 [h,ty,k,l,r] →
    Supplies body Γ goal (fun β j Δ => NumberedNoHeadFacts s body Δ
      (p.relabel j) (ty.relabel j) (k.relabel j) (l.relabel j) (r.relabel j))

def ExactCoverHeadFittedWindowCalibrated : Prop :=
  ∀ (s : Settings) (B : Program 2) (T : Program 1), GrammarTypeInclusion s →
    IntrinsicWindowCalibrated s B → TypeGuardCalibrated s T →
    ActualPackedWindow s (headFittedWindow s B T)

def ExactOpenCoverHeadFittedDispatch : Prop :=
  ∀ (V TV M : Program 1) (B : Program 2) (T : Program 1) (s : Settings)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (raw p vertices ctx result : OTerm α),
    let P := headPrograms s V TV M B T
    RemainingWithoutHeads P s body →
    ParentRow P s body Γ raw p vertices ctx result →
    Nonempty (Derivation body Γ (memberGraph vertices raw))

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverHeadDispatchTargets
