module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLocalOwnContinuationTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverOwnEarlierTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalStrongInduction (below)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open ID1Completion.InternalClosedPrograms (allBlock)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc z)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalFactoredAuxOwnCoverTargets (typesTerm)
open NumberedWindowInternalCoverLambdaLayerTargets (lambdaTerm)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalCoverLambdaDerivedOwnTargets (lambdaOwnClause lambdaLocalIH)
open NumberedWindowInternalCoverRefinedSharedSyntaxTargets (refinedSyntax)
open NumberedWindowInternalCoverSharedRecursionTargets (sharedMeasureUpdate)
open NumberedWindowInternalStrictAuxWindowTargets (strictAuxWindow)
open NumberedWindowInternalCoverLocalOwnContinuationTargets (refinedCover ActualOwnParent)

/-- Quantify context, result type, actual scratch result, in that order.
The raw key remains the single course-of-values induction index. -/
def ownMatrix (W C : Program 3) (s : Settings) {α : Type} (q : OTerm α) :
    Formula (α ⊕ Fin 3) :=
  lambdaOwnClause W C s (.var (.inr 0)) (.var (.inr 1)) (q.relabel Sum.inl) (.var (.inr 2))

def ownAll (W C : Program 3) (s : Settings) {α : Type} (q : OTerm α) : Formula α :=
  allBlock (ownMatrix W C s q)

def ownAt (V : Program 1) (W C : Program 3) (s : Settings) {α : Type} (q : OTerm α) : Formula α :=
  (unary V (suc z) q).imp (ownAll W C s q)

def ownMotive (V : Program 1) (W C : Program 3) (s : Settings) {α : Type} : Formula (α ⊕ Fin 1) :=
  ownAt V W C s (.var (.inr 0))

abbrev ownBelow (V : Program 1) (W C : Program 3) (s : Settings) {α : Type} (q : OTerm α) :
    Formula α := below (ownMotive V W C s) q

/-- Specialize the original object induction hypothesis at a real earlier
key, paying actual validity. Its typed/scratch antecedents remain as
formulas, not derived or assumed by the specialization. -/
def ExactOpenCoverOwnEarlierLocalIH : Prop :=
  ∀ (V : Program 1) (W C : Program 3) (s : Settings)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (ctx ty child parent : OTerm α),
    Nonempty (Derivation body Γ (ownBelow V W C s parent)) →
    Nonempty (Derivation body Γ (ltF child parent)) →
    Nonempty (Derivation body Γ (unary V (suc z) child)) →
    Nonempty (Derivation body Γ (lambdaLocalIH W C s ctx ty child))

def ExactOpenCoverRefinedLambdaOwnEarlier : Prop :=
  ∀ (V TV M : Program 1) (W : Program 3) (s : Settings) (body : Positive (Fin 1))
    (α : Type) (Γ : List (Formula α)) (p vertices ctx bodyTy ty q : OTerm α),
    ActualOwnParent (refinedSyntax V TV) (sharedMeasureUpdate M) s body Γ (lambdaTerm ty q) p vertices →
    Nonempty (Derivation body Γ (ownBelow (refinedSyntax V TV) W (refinedCover V TV M) s (lambdaTerm ty q))) →
    Nonempty (Derivation body Γ (windowAt W ctx bodyTy q)) →
    Nonempty (Derivation body Γ (memberGraph (typesTerm s α) ty)) →
    Nonempty (Derivation body Γ (memberGraph vertices (lambdaTerm ty q)))

def ExactOpenCoverRefinedAuxOwnEarlier : Prop :=
  ∀ (V TV M : Program 1) (B : Program 2) (TW : Program 1) (s : Settings)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (p vertices ctx dom cod fn arg : OTerm α),
    ActualOwnParent (refinedSyntax V TV) (sharedMeasureUpdate M) s body Γ (auxiliaryTerm dom cod fn arg) p vertices →
    Nonempty (Derivation body Γ
      (ownBelow (refinedSyntax V TV) (strictAuxWindow B TW) (refinedCover V TV M) s (auxiliaryTerm dom cod fn arg))) →
    Nonempty (Derivation body Γ (windowAt (strictAuxWindow B TW) ctx cod (auxiliaryTerm dom cod fn arg))) →
    Nonempty (Derivation body Γ (memberGraph (typesTerm s α) dom)) →
    Nonempty (Derivation body Γ (memberGraph (typesTerm s α) cod)) →
    Nonempty (Derivation body Γ (memberGraph vertices (auxiliaryTerm dom cod fn arg)))

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverOwnEarlierTargets
