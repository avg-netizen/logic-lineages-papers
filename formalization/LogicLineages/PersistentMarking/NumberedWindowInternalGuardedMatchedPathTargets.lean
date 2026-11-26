module
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoveredFormationTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseIntrinsicInstallationTargets
@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalGuardedMatchedPathTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary rawCons suc z)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalAuxWindowMemoTargets (selectedIntrinsic)
open NumberedWindowInternalAuxWindowStepTargets (windowUpdate intrinsicQuery)
open NumberedWindowInternalOwnCoverReportsTargets (syntaxFlag)
open NumberedWindowInternalFactoredCoverTargets (factoredCover)
open NumberedWindowInternalSparseStructuralApplicationTargets (window)
open NumberedWindowInternalSparseCoverOccurrenceTargets (occursInCover)


open SourceComputabilityFormulaSupportProof (allOne)
open NumberedWindowInternalSparseFormationRepresentativeTargets (formation)
open NumberedWindowInternalSparseMatchedPathTargets (MatchedPathAt)
open NumberedWindowInternalSparseMatchedCallsTargets (pulled)
open NumberedWindowInternalSparsePositiveHeadDecompositionTargets (positiveAt)
open NumberedWindowInternalSparsePackedLeast (packedLeastProgram)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)

def parentCoverage {α : Type} (C : Program 3) (s : Settings) (W : Program 3) (ctx dom cod arg : OTerm α) : Formula α :=
  let j : α → α ⊕ Fin 1 := Sum.inl
  let f : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let parent := auxiliaryTerm (dom.relabel j) (cod.relabel j) f (arg.relabel j)
  allOne ((windowAt W (ctx.relabel j) ((rawCons dom cod).relabel j) f).imp (occursInCover C s parent parent))

def support {α : Type} (C : Program 3) (s : Settings) (W : Program 3) (T : Program 1)
    (ctx dom cod arg : OTerm α) : Formula α :=
  (((unary T (suc z) dom ⊓ unary T (suc z) cod) ⊓ windowAt W ctx dom arg) ⊓
    parentCoverage C s W ctx dom cod arg)

def ExactGuardedFormation : Prop := ∀ (baseV M : Program 1) (G : Program 3) (s : Settings)
    (intrinsicBase : Program 2) (T : Program 1) (body : Positive (Fin 1)) (α : Type)
    (Γ : List (Formula α)) (ctx dom cod arg : OTerm α),
  let V := syntaxFlag baseV
  let C := factoredCover V M G
  let K := intrinsicQuery (selectedIntrinsic (windowUpdate intrinsicBase T))
  let W := window C s K V
  Nonempty (Derivation body Γ ((support C s W T ctx dom cod arg).imp (formation W ctx dom cod arg)))

def GuardedPathAt (C : Program 3) (s : Settings) (X : Program 2) (W : Program 3) (T : Program 1) (raw : Program 5) : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (ctx dom cod arg fn next cert value : OTerm α),
    let positive := positiveAt raw (packedLeastProgram C X W s) ctx (rawCons dom cod) fn cert next
    let later := leastGraph C X W s ctx cod (auxiliaryTerm dom cod next arg) value
    Nonempty (Derivation body Γ ((support C s W T ctx dom cod arg ⊓ (positive ⊓ later)).imp
      (pulled C X W s raw ctx cod (auxiliaryTerm dom cod fn arg) value)))

def ExactGuardedPath : Prop := ∀ (baseV M : Program 1) (G : Program 3) (s : Settings)
    (intrinsicBase : Program 2) (T : Program 1) (X : Program 2) (raw : Program 5),
  let V := syntaxFlag baseV
  let C := factoredCover V M G
  let K := intrinsicQuery (selectedIntrinsic (windowUpdate intrinsicBase T))
  let W := window C s K V
  MatchedPathAt C X W s raw → GuardedPathAt C s X W T raw

end LogicLineages.PersistentMarking.NumberedWindowInternalGuardedMatchedPathTargets
