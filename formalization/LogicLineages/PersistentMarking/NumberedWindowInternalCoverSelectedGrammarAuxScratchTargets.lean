module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarOptionTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarAuxParentTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalFactoredAuxOwnCoverTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarAuxScratchTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary)
open NumberedWindowInternalSparseCoverScratch (coverOption scratchVertices)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalFactoredCoverTargets (factoredCover)
open NumberedWindowInternalFactoredAuxOwnCoverTargets (headsTerm typesTerm measurePair)
open NumberedWindowInternalCoverSelectedGrammarWidthTargets (observed)
open NumberedWindowInternalCoverSelectedGrammarOptionTargets (selectedGrammarOption)

/-- The same originally factored cover with the physical chosen option
callback, not a new accepted status or another scratch producer. -/
abbrev selectedCover (V Measure : Program 1) := factoredCover V Measure selectedGrammarOption

/-- Actual supplied local evidence only. No field is a universal child
own-cover or witness/typing/measurement-provenance assertion. -/
structure AuxParentInputs (V Measure : Program 1) (s : Settings)
    (body : Positive (Fin 1)) {α : Type} (Γ : List (Formula α))
    (m d maxNumeral df mf da ma fState fTerms fArgs aState aTerms aArgs dom cod fn arg : OTerm α) : Prop where
  functionReport : Nonempty (Derivation body Γ
    (observed df (headsTerm s α) (typesTerm s α) mf fState fTerms fArgs))
  argumentReport : Nonempty (Derivation body Γ
    (observed da (headsTerm s α) (typesTerm s α) ma aState aTerms aArgs))
  functionMember : Nonempty (Derivation body Γ (memberGraph fTerms fn))
  argumentMember : Nonempty (Derivation body Γ (memberGraph aTerms arg))
  functionDepth : Nonempty (Derivation body Γ (ltF df (suc d)))
  functionWidth : Nonempty (Derivation body Γ (ltF mf (suc maxNumeral)))
  argumentDepth : Nonempty (Derivation body Γ (ltF da (suc d)))
  argumentWidth : Nonempty (Derivation body Γ (ltF ma (suc maxNumeral)))
  domainMember : Nonempty (Derivation body Γ (memberGraph (typesTerm s α) dom))
  codomainMember : Nonempty (Derivation body Γ (memberGraph (typesTerm s α) cod))
  validity : Nonempty (Derivation body Γ (unary V (suc z) (auxiliaryTerm dom cod fn arg)))
  measure : Nonempty (Derivation body Γ (unary Measure m (auxiliaryTerm dom cod fn arg)))
  measureCode : Nonempty (Derivation body Γ (measurePair m d maxNumeral))

/-- The observed chosen successor's vertices are the option payload and
the actual scratch output, and contain the unchanged literal parent key. -/
def ExactOpenSelectedGrammarAuxScratchAtObserved : Prop :=
  ∀ (V Measure : Program 1) (s : Settings) (body : Positive (Fin 1)) (α : Type)
    (Γ : List (Formula α)) (m d maxNumeral df mf da ma fState fTerms fArgs aState aTerms aArgs
      prev prevTerms prevArgs next vertices nextArgs dom cod fn arg : OTerm α),
  let C := selectedCover V Measure
  let parent := auxiliaryTerm dom cod fn arg
  AuxParentInputs V Measure s body Γ m d maxNumeral df mf da ma fState fTerms fArgs aState aTerms aArgs dom cod fn arg →
  Nonempty (Derivation body Γ (observed d (headsTerm s α) (typesTerm s α)
    maxNumeral prev prevTerms prevArgs)) →
  Nonempty (Derivation body Γ (observed (suc d) (headsTerm s α) (typesTerm s α)
    maxNumeral next vertices nextArgs)) →
  Nonempty (Derivation body Γ
    (unary (coverOption C s) (suc vertices) parent ⊓
     (unary (scratchVertices C s) vertices parent ⊓ memberGraph vertices parent)))

/-- A supplied actual chosen scratch report need not be reconstructed by
the caller. It is aligned with the same physical chosen grammar output
by original graph functionality, never by a numerical equality. -/
def ExactOpenSelectedGrammarAuxScratchMembership : Prop :=
  ∀ (V Measure : Program 1) (s : Settings) (body : Positive (Fin 1)) (α : Type)
    (Γ : List (Formula α)) (m d maxNumeral df mf da ma fState fTerms fArgs aState aTerms aArgs
      vertices dom cod fn arg : OTerm α),
  let C := selectedCover V Measure
  let parent := auxiliaryTerm dom cod fn arg
  AuxParentInputs V Measure s body Γ m d maxNumeral df mf da ma fState fTerms fArgs aState aTerms aArgs dom cod fn arg →
  Nonempty (Derivation body Γ (unary (scratchVertices C s) vertices parent)) →
  Nonempty (Derivation body Γ (memberGraph vertices parent))

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarAuxScratchTargets
