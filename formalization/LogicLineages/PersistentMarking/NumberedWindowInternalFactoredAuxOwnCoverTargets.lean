module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverGrammarStageTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverScratchOpenTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalFactoredAuxOwnCoverTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open SourceComputabilityFormulaSupportProof (numeral)
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary)
open NumberedWindowInternalSparseCoverScratch (coverOption scratchVertices)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalFactoredCoverTargets (factoredCover)
open NumberedWindowInternalCoverGrammarStageTargets (stageGenerator termsGraph)

abbrev headsTerm (s : Settings) (α : Type) : OTerm α := numeral (Encodable.encode s.window.2)
abbrev typesTerm (s : Settings) (α : Type) : OTerm α := numeral (Encodable.encode s.types)

abbrev installedCover (V M : Program 1) (P : Program 5) (A : Program 2) :=
  factoredCover V M (stageGenerator P A)

abbrev measurePair {α : Type} (m depth maxNumeral : OTerm α) :=
  programGraph ID1Completion.InternalPairing.pairing m ![suc depth,maxNumeral]

/-- At the literal auxiliary parent whose actual measure is the unshifted
pair (successor depth, numeral bound), install the genuine successor
grammar terms into the original option and physical scratch programs.
The incoming occurrences must already be present under those exact grammar
bounds; type occurrences are in the original grammar type list, not inferred
from an intrinsic window check. -/
def ExactOpenFactoredAuxCoverAtTerms : Prop :=
  ∀ (V M : Program 1) (P : Program 5) (A : Program 2) (s : Settings)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (m depth maxNumeral prev vertices dom cod fn arg : OTerm α),
    let parent := auxiliaryTerm dom cod fn arg
    let C := installedCover V M P A
    Nonempty (Derivation body Γ (unary V (suc z) parent)) →
    Nonempty (Derivation body Γ (unary M m parent)) →
    Nonempty (Derivation body Γ (measurePair m depth maxNumeral)) →
    Nonempty (Derivation body Γ
      (termsGraph P A prev depth (headsTerm s α) (typesTerm s α) maxNumeral)) →
    Nonempty (Derivation body Γ
      (termsGraph P A vertices (suc depth) (headsTerm s α) (typesTerm s α) maxNumeral)) →
    Nonempty (Derivation body Γ (memberGraph (typesTerm s α) dom)) →
    Nonempty (Derivation body Γ (memberGraph (typesTerm s α) cod)) →
    Nonempty (Derivation body Γ (memberGraph prev fn)) →
    Nonempty (Derivation body Γ (memberGraph prev arg)) →
    Nonempty (Derivation body Γ
      (unary (coverOption C s) (suc vertices) parent ⊓
        (unary (scratchVertices C s) vertices parent ⊓ memberGraph vertices parent)))

/-- For a preexisting actual scratch report, no explicit successor-terms
report is needed: graph totality and uniqueness align it with the same
physical grammar report. This is not unconditional own-cover membership:
same-bound predecessor occurrences and literal grammar type entries remain. -/
def ExactOpenFactoredAuxCoverMembership : Prop :=
  ∀ (V M : Program 1) (P : Program 5) (A : Program 2) (s : Settings)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (m depth maxNumeral prev vertices dom cod fn arg : OTerm α),
    let parent := auxiliaryTerm dom cod fn arg
    let C := installedCover V M P A
    Nonempty (Derivation body Γ (unary V (suc z) parent)) →
    Nonempty (Derivation body Γ (unary M m parent)) →
    Nonempty (Derivation body Γ (measurePair m depth maxNumeral)) →
    Nonempty (Derivation body Γ
      (termsGraph P A prev depth (headsTerm s α) (typesTerm s α) maxNumeral)) →
    Nonempty (Derivation body Γ (memberGraph (typesTerm s α) dom)) →
    Nonempty (Derivation body Γ (memberGraph (typesTerm s α) cod)) →
    Nonempty (Derivation body Γ (memberGraph prev fn)) →
    Nonempty (Derivation body Γ (memberGraph prev arg)) →
    Nonempty (Derivation body Γ (unary (scratchVertices C s) vertices parent)) →
    Nonempty (Derivation body Γ (memberGraph vertices parent))

end LogicLineages.PersistentMarking.NumberedWindowInternalFactoredAuxOwnCoverTargets
