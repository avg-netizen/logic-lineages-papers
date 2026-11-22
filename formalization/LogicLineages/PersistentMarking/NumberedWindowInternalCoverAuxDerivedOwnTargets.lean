module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarAuxScratchMeasuredTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaDerivedOwnTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxSyntaxTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalStrictAuxWindowParentTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureParentTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxDerivedOwnTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary z suc rawCons)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparseCoverScratch (scratchVertices)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalFactoredAuxOwnCoverTargets (headsTerm typesTerm)
open NumberedWindowInternalCoverSelectedGrammarWidthTargets (observed)
open NumberedWindowInternalCoverSelectedGrammarAuxScratchTargets (selectedCover)
open NumberedWindowInternalCoverSelectedGrammarAuxScratchMeasuredTargets (chosenMeasure MeasuredChild)
open NumberedWindowInternalCoverLambdaDerivedOwnTargets (lambdaLocalIH)
open NumberedWindowInternalCoverAuxSyntaxTargets (auxSyntax)
open NumberedWindowInternalChosenAuxMeasureCombine (chosenCombine)
open NumberedWindowInternalChosenAuxMeasureParentTargets (AuxMeasureChild)
open NumberedWindowInternalAuxMeasureOpenTargets (measureGraph)
open NumberedWindowInternalStrictAuxWindowTargets (strictAuxWindow)

abbrev auxCover (V TV M : Program 1) : Program 3 :=
  selectedCover (auxSyntax V TV) (chosenMeasure M)

/-- The local induction clause is the exact existing object quantifier
over the single scratch output at this very typed key. -/
structure LocalChild (V TV M : Program 1) (W : Program 3) (s : Settings)
    (body : Positive (Fin 1)) {α : Type} (Γ : List (Formula α)) (ctx ty q : OTerm α) : Prop where
  valid : Nonempty (Derivation body Γ (unary (auxSyntax V TV) (suc z) q))
  typed : Nonempty (Derivation body Γ (windowAt W ctx ty q))
  ih : Nonempty (Derivation body Γ (lambdaLocalIH W (auxCover V TV M) s ctx ty q))

def ExactOpenCoverAuxMeasuredChild : Prop :=
  ∀ (V TV M : Program 1) (W : Program 3) (s : Settings) (body : Positive (Fin 1))
    (α : Type) (Γ : List (Formula α)) (ctx ty q m d width state terms args : OTerm α),
    LocalChild V TV M W s body Γ ctx ty q →
    AuxMeasureChild M body Γ q m d width →
    Nonempty (Derivation body Γ (observed d (headsTerm s α) (typesTerm s α) width state terms args)) →
    MeasuredChild M s body Γ m d width state terms args q

def ExactOpenCoverAuxMeasuredChildCases : Prop :=
  ∀ (V TV M : Program 1) (W : Program 3) (s : Settings) (body : Positive (Fin 1))
    (α : Type) (Γ : List (Formula α)) (ctx ty q m d width : OTerm α) (goal : Formula α),
    LocalChild V TV M W s body Γ ctx ty q →
    AuxMeasureChild M body Γ q m d width →
    (∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (state terms args : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      MeasuredChild M s body Δ (m.relabel j) (d.relabel j) (width.relabel j)
        state terms args (q.relabel j) →
      Nonempty (Derivation body Δ (goal.relabel j))) →
    Nonempty (Derivation body Γ goal)

/-- Actual three independent parent reports, two actual K members,
and two local typed scratch IHs. TV and TW are intentionally independent
programs: respectively syntax type-bit and scalar typed window guards. -/
structure Inputs (V TV M : Program 1) (B : Program 2) (TW : Program 1) (s : Settings)
    (body : Positive (Fin 1)) {α : Type} (Γ : List (Formula α))
    (p vertices ctx dom cod fn arg : OTerm α) : Prop where
  valid : Nonempty (Derivation body Γ (unary (auxSyntax V TV) (suc z) (auxiliaryTerm dom cod fn arg)))
  measured : Nonempty (Derivation body Γ (measureGraph M chosenCombine p (auxiliaryTerm dom cod fn arg)))
  typed : Nonempty (Derivation body Γ (windowAt (strictAuxWindow B TW) ctx cod (auxiliaryTerm dom cod fn arg)))
  fnIH : Nonempty (Derivation body Γ
    (lambdaLocalIH (strictAuxWindow B TW) (auxCover V TV M) s ctx (rawCons dom cod) fn))
  argIH : Nonempty (Derivation body Γ
    (lambdaLocalIH (strictAuxWindow B TW) (auxCover V TV M) s ctx dom arg))
  domMember : Nonempty (Derivation body Γ (memberGraph (typesTerm s α) dom))
  codMember : Nonempty (Derivation body Γ (memberGraph (typesTerm s α) cod))
  held : Nonempty (Derivation body Γ (unary (scratchVertices (auxCover V TV M) s) vertices
    (auxiliaryTerm dom cod fn arg)))

def ExactOpenCoverAuxDerivedOwn : Prop :=
  ∀ (V TV M : Program 1) (B : Program 2) (TW : Program 1) (s : Settings)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (p vertices ctx dom cod fn arg : OTerm α),
    Inputs V TV M B TW s body Γ p vertices ctx dom cod fn arg →
    Nonempty (Derivation body Γ (memberGraph vertices (auxiliaryTerm dom cod fn arg)))

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxDerivedOwnTargets
