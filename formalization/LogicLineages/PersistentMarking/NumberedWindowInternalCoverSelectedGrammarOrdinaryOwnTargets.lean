module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarAuxScratchTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverOrdinaryLayerTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarOrdinaryOwnTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary)
open NumberedWindowInternalSparseCoverScratch (scratchVertices)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalCoverOrdinaryLayerTargets (taggedTerm)
open NumberedWindowInternalFactoredAuxOwnCoverTargets (headsTerm typesTerm measurePair)
open NumberedWindowInternalCoverSelectedSuccessorTargets (stepReport)
open NumberedWindowInternalCoverSelectedGrammarWidthTargets (observed)
open NumberedWindowInternalCoverSelectedGrammarAuxScratchTargets (selectedCover)

abbrev ordinaryKey {α : Type} (h a : OTerm α) := taggedTerm 4 h a

def OpenSelectedPartContainsOrdinary (P : Program 5) : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (out H K ids terms args h a : OTerm α),
    Nonempty (Derivation body Γ (stepReport P out H K ids terms args)) →
    Nonempty (Derivation body Γ (memberGraph H h)) →
    Nonempty (Derivation body Γ (memberGraph args a)) →
    Nonempty (Derivation body Γ (memberGraph out (ordinaryKey h a)))

def ExactOpenSelectedGrammarOrdinaryFromPredecessor : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (d H K M prev prevTerms prevArgs next out nextArgs h a : OTerm α),
    Nonempty (Derivation body Γ (observed d H K M prev prevTerms prevArgs)) →
    Nonempty (Derivation body Γ (observed (suc d) H K M next out nextArgs)) →
    Nonempty (Derivation body Γ (memberGraph H h)) →
    Nonempty (Derivation body Γ (memberGraph prevArgs a)) →
    Nonempty (Derivation body Γ (memberGraph out (ordinaryKey h a)))

def ExactOpenSelectedGrammarOrdinaryAtBounds : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (d H K M da Ma aState aTerms aArgs prev prevTerms prevArgs next out nextArgs h a : OTerm α),
    Nonempty (Derivation body Γ (observed da H K Ma aState aTerms aArgs)) →
    Nonempty (Derivation body Γ (memberGraph aArgs a)) →
    Nonempty (Derivation body Γ (ltF da (suc d))) →
    Nonempty (Derivation body Γ (ltF Ma (suc M))) →
    Nonempty (Derivation body Γ (observed d H K M prev prevTerms prevArgs)) →
    Nonempty (Derivation body Γ (observed (suc d) H K M next out nextArgs)) →
    Nonempty (Derivation body Γ (memberGraph H h)) →
    Nonempty (Derivation body Γ (memberGraph out (ordinaryKey h a)))

/-- Actual argument scope and membership, exact parent measure and
guard, not a measurement or typing provenance theorem. -/
structure OrdinaryOwnInputs (V Measure : Program 1) (s : Settings)
    (body : Positive (Fin 1)) {α : Type} (Γ : List (Formula α))
    (m d M da Ma aState aTerms aArgs h a : OTerm α) : Prop where
  argumentScope : Nonempty (Derivation body Γ (observed da (headsTerm s α) (typesTerm s α) Ma
    aState aTerms aArgs))
  argumentHit : Nonempty (Derivation body Γ (memberGraph aArgs a))
  argumentDepth : Nonempty (Derivation body Γ (ltF da (suc d)))
  argumentWidth : Nonempty (Derivation body Γ (ltF Ma (suc M)))
  headHit : Nonempty (Derivation body Γ (memberGraph (headsTerm s α) h))
  validity : Nonempty (Derivation body Γ (unary V (suc z) (ordinaryKey h a)))
  measurement : Nonempty (Derivation body Γ (unary Measure m (ordinaryKey h a)))
  parentPair : Nonempty (Derivation body Γ (measurePair m d M))

def ExactOpenSelectedGrammarOrdinaryScratch : Prop :=
  ∀ (V Measure : Program 1) (s : Settings) (body : Positive (Fin 1)) (α : Type)
    (Γ : List (Formula α)) (m d M da Ma aState aTerms aArgs vertices h a : OTerm α),
    OrdinaryOwnInputs V Measure s body Γ m d M da Ma aState aTerms aArgs h a →
    Nonempty (Derivation body Γ
      (unary (scratchVertices (selectedCover V Measure) s) vertices (ordinaryKey h a))) →
    Nonempty (Derivation body Γ (memberGraph vertices (ordinaryKey h a)))

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarOrdinaryOwnTargets
