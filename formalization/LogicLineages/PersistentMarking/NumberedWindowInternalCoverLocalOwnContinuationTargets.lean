module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSharedOwnScratchTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverRefinedSharedSyntaxTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverLocalOwnContinuationTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc z)
open SourceComputabilityFormulaSupportProof (existsOne)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary rawCons)
open NumberedWindowInternalSparseCoverScratch (scratchVertices)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalFactoredAuxOwnCoverTargets (typesTerm)
open NumberedWindowInternalCoverSelectedGrammarAuxScratchTargets (selectedCover)
open NumberedWindowInternalCoverLambdaLayerTargets (lambdaTerm)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalCoverLambdaDerivedOwnTargets (lambdaLocalIH)
open NumberedWindowInternalAuxMeasureMemoTargets (selectedMeasure)
open NumberedWindowInternalStrictAuxWindowTargets (strictAuxWindow)
open NumberedWindowInternalChosenAuxMeasureCombineOpenTargets (codePair boundBody)
open NumberedWindowInternalCoverSharedMeasureChildrenTargets (SelectedMeasureData)
open NumberedWindowInternalCoverSharedRecursionTargets (sharedMeasure sharedMeasureUpdate)
open NumberedWindowInternalCoverSharedOwnScratchTargets (ChildOwnInputs)
open NumberedWindowInternalCoverRefinedSharedSyntaxTargets (refinedSyntax)

structure ActualOwnParent (V : Program 1) (R : Program 4) (s : Settings)
    (body : Positive (Fin 1)) {α : Type} (Γ : List (Formula α)) (key p vertices : OTerm α) : Prop where
  valid : Nonempty (Derivation body Γ (unary V (suc z) key))
  measured : Nonempty (Derivation body Γ (unary (selectedMeasure R) p key))
  held : Nonempty (Derivation body Γ (unary (scratchVertices (selectedCover V (selectedMeasure R)) s) vertices key))

def ExactOpenCoverLocalLambdaOwnContinuation : Prop :=
  ∀ (V : Program 1) (R : Program 4) (W : Program 3) (s : Settings)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (p vertices ctx bodyTy ty q mc d b : OTerm α),
    ActualOwnParent V R s body Γ (lambdaTerm ty q) p vertices →
    ChildOwnInputs V R W s body Γ ctx bodyTy q →
    SelectedMeasureData R body Γ q mc d b →
    Nonempty (Derivation body Γ (codePair p (suc d) b)) →
    Nonempty (Derivation body Γ (memberGraph (typesTerm s α) ty)) →
    Nonempty (Derivation body Γ (memberGraph vertices (lambdaTerm ty q)))

def ExactOpenCoverLocalAuxOwnContinuation : Prop :=
  ∀ (V : Program 1) (R : Program 4) (W : Program 3) (s : Settings)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (p vertices ctx dom cod fn arg mf ma df da bf ba : OTerm α),
    ActualOwnParent V R s body Γ (auxiliaryTerm dom cod fn arg) p vertices →
    ChildOwnInputs V R W s body Γ ctx (rawCons dom cod) fn →
    ChildOwnInputs V R W s body Γ ctx dom arg →
    SelectedMeasureData R body Γ fn mf df bf →
    SelectedMeasureData R body Γ arg ma da ba →
    Nonempty (Derivation body Γ (existsOne (boundBody p df da bf ba))) →
    Nonempty (Derivation body Γ (memberGraph (typesTerm s α) dom)) →
    Nonempty (Derivation body Γ (memberGraph (typesTerm s α) cod)) →
    Nonempty (Derivation body Γ (memberGraph vertices (auxiliaryTerm dom cod fn arg)))

abbrev refinedCover (V TV M : Program 1) : Program 3 :=
  selectedCover (refinedSyntax V TV) (sharedMeasure M)

def ExactOpenCoverRefinedLambdaOwnScratch : Prop :=
  ∀ (V TV M : Program 1) (W : Program 3) (s : Settings) (body : Positive (Fin 1))
    (α : Type) (Γ : List (Formula α)) (p vertices ctx bodyTy ty q : OTerm α),
    ActualOwnParent (refinedSyntax V TV) (sharedMeasureUpdate M) s body Γ (lambdaTerm ty q) p vertices →
    Nonempty (Derivation body Γ (windowAt W ctx bodyTy q)) →
    Nonempty (Derivation body Γ (lambdaLocalIH W (refinedCover V TV M) s ctx bodyTy q)) →
    Nonempty (Derivation body Γ (memberGraph (typesTerm s α) ty)) →
    Nonempty (Derivation body Γ (memberGraph vertices (lambdaTerm ty q)))

def ExactOpenCoverRefinedAuxOwnScratch : Prop :=
  ∀ (V TV M : Program 1) (B : Program 2) (TW : Program 1) (s : Settings)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (p vertices ctx dom cod fn arg : OTerm α),
    ActualOwnParent (refinedSyntax V TV) (sharedMeasureUpdate M) s body Γ (auxiliaryTerm dom cod fn arg) p vertices →
    Nonempty (Derivation body Γ (windowAt (strictAuxWindow B TW) ctx cod (auxiliaryTerm dom cod fn arg))) →
    Nonempty (Derivation body Γ
      (lambdaLocalIH (strictAuxWindow B TW) (refinedCover V TV M) s ctx (rawCons dom cod) fn)) →
    Nonempty (Derivation body Γ
      (lambdaLocalIH (strictAuxWindow B TW) (refinedCover V TV M) s ctx dom arg)) →
    Nonempty (Derivation body Γ (memberGraph (typesTerm s α) dom)) →
    Nonempty (Derivation body Γ (memberGraph (typesTerm s α) cod)) →
    Nonempty (Derivation body Γ (memberGraph vertices (auxiliaryTerm dom cod fn arg)))

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverLocalOwnContinuationTargets
