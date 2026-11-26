module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSharedMeasureChildrenTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaDerivedOwnTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarAuxScratchTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalStrictAuxWindowParentTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSharedOwnScratchTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary rawCons)
open NumberedWindowInternalSparseCoverScratch (scratchVertices)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalCoverSelectedGrammarAuxScratchTargets (selectedCover)
open NumberedWindowInternalCoverSelectedGrammarWidthTargets (observed)
open NumberedWindowInternalFactoredAuxOwnCoverTargets (headsTerm typesTerm)
open NumberedWindowInternalCoverLambdaLayerTargets (lambdaTerm)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalCoverLambdaDerivedOwnTargets (lambdaLocalIH)
open NumberedWindowInternalCoverSharedRecursionTargets
open NumberedWindowInternalAuxMeasureMemoTargets (selectedMeasure)
open NumberedWindowInternalStrictAuxWindowTargets (strictAuxWindow)

abbrev sharedCover (V TV M : Program 1) : Program 3 :=
  selectedCover (sharedSyntax V TV) (sharedMeasure M)

/-- An original selected grammar observation and the occurrence on its
actual term list, after a single local IH is applied to its physical scratch. -/
structure OwnOccurrence (s : Settings) (body : Positive (Fin 1))
    {α : Type} (Γ : List (Formula α)) (d b state terms args key : OTerm α) : Prop where
  observedScope : Nonempty (Derivation body Γ (observed d (headsTerm s α) (typesTerm s α) b state terms args))
  ownKey : Nonempty (Derivation body Γ (memberGraph terms key))

structure ChildOwnInputs (V : Program 1) (R : Program 4) (W : Program 3) (s : Settings)
    (body : Positive (Fin 1)) {α : Type} (Γ : List (Formula α)) (ctx ty key : OTerm α) : Prop where
  valid : Nonempty (Derivation body Γ (unary V (suc z) key))
  typed : Nonempty (Derivation body Γ (windowAt W ctx ty key))
  ih : Nonempty (Derivation body Γ (lambdaLocalIH W (selectedCover V (selectedMeasure R)) s ctx ty key))

open NumberedWindowInternalCoverSharedMeasureChildrenTargets (SelectedMeasureData)

def ExactOpenCoverChildOwnScopeCases : Prop :=
  ∀ (V : Program 1) (R : Program 4) (W : Program 3) (s : Settings)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (ctx ty key m d b : OTerm α) (goal : Formula α),
    ChildOwnInputs V R W s body Γ ctx ty key →
    SelectedMeasureData R body Γ key m d b →
    (∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (state terms args : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      OwnOccurrence s body Δ (d.relabel j) (b.relabel j) state terms args (key.relabel j) →
      Nonempty (Derivation body Δ (goal.relabel j))) →
    Nonempty (Derivation body Γ goal)

structure LambdaInputs (V TV M : Program 1) (W : Program 3) (s : Settings) (body : Positive (Fin 1))
    {α : Type} (Γ : List (Formula α)) (p vertices ctx bodyTy ty q : OTerm α) : Prop where
  valid : Nonempty (Derivation body Γ (unary (sharedSyntax V TV) (suc z) (lambdaTerm ty q)))
  measured : Nonempty (Derivation body Γ (unary (sharedMeasure M) p (lambdaTerm ty q)))
  typedBody : Nonempty (Derivation body Γ (windowAt W ctx bodyTy q))
  bodyIH : Nonempty (Derivation body Γ (lambdaLocalIH W (sharedCover V TV M) s ctx bodyTy q))
  typeMember : Nonempty (Derivation body Γ (memberGraph (typesTerm s α) ty))
  held : Nonempty (Derivation body Γ (unary (scratchVertices (sharedCover V TV M) s) vertices (lambdaTerm ty q)))

structure AuxInputs (V TV M : Program 1) (B : Program 2) (TW : Program 1) (s : Settings)
    (body : Positive (Fin 1)) {α : Type} (Γ : List (Formula α))
    (p vertices ctx dom cod fn arg : OTerm α) : Prop where
  valid : Nonempty (Derivation body Γ (unary (sharedSyntax V TV) (suc z) (auxiliaryTerm dom cod fn arg)))
  measured : Nonempty (Derivation body Γ (unary (sharedMeasure M) p (auxiliaryTerm dom cod fn arg)))
  typed : Nonempty (Derivation body Γ (windowAt (strictAuxWindow B TW) ctx cod (auxiliaryTerm dom cod fn arg)))
  fnIH : Nonempty (Derivation body Γ
    (lambdaLocalIH (strictAuxWindow B TW) (sharedCover V TV M) s ctx (rawCons dom cod) fn))
  argIH : Nonempty (Derivation body Γ
    (lambdaLocalIH (strictAuxWindow B TW) (sharedCover V TV M) s ctx dom arg))
  domMember : Nonempty (Derivation body Γ (memberGraph (typesTerm s α) dom))
  codMember : Nonempty (Derivation body Γ (memberGraph (typesTerm s α) cod))
  held : Nonempty (Derivation body Γ (unary (scratchVertices (sharedCover V TV M) s) vertices
    (auxiliaryTerm dom cod fn arg)))

def ExactOpenCoverSharedLambdaOwnScratch : Prop :=
  ∀ (V TV M : Program 1) (W : Program 3) (s : Settings) (body : Positive (Fin 1))
    (α : Type) (Γ : List (Formula α)) (p vertices ctx bodyTy ty q : OTerm α),
    LambdaInputs V TV M W s body Γ p vertices ctx bodyTy ty q →
    Nonempty (Derivation body Γ (memberGraph vertices (lambdaTerm ty q)))

def ExactOpenCoverSharedAuxOwnScratch : Prop :=
  ∀ (V TV M : Program 1) (B : Program 2) (TW : Program 1) (s : Settings)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (p vertices ctx dom cod fn arg : OTerm α),
    AuxInputs V TV M B TW s body Γ p vertices ctx dom cod fn arg →
    Nonempty (Derivation body Γ (memberGraph vertices (auxiliaryTerm dom cod fn arg)))

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSharedOwnScratchTargets
