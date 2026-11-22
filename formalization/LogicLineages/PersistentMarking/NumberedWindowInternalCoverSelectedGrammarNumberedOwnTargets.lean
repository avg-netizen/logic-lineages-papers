module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarAuxScratchTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedLayerTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarNumberedOwnTargets
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
open NumberedWindowInternalCoverNumberedLayerTargets (numberedTerm)
open NumberedWindowInternalFactoredAuxOwnCoverTargets (headsTerm typesTerm measurePair)
open NumberedWindowInternalCoverSelectedSuccessorTargets (stepReport)
open NumberedWindowInternalCoverSelectedGrammarWidthTargets (observed)
open NumberedWindowInternalCoverSelectedGrammarAuxScratchTargets (selectedCover)

def OpenSelectedPartContainsNumbered (P : Program 5) : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (out H K ids terms args h ty k l r : OTerm α),
    Nonempty (Derivation body Γ (stepReport P out H K ids terms args)) →
    Nonempty (Derivation body Γ (memberGraph H h)) →
    Nonempty (Derivation body Γ (memberGraph K ty)) →
    Nonempty (Derivation body Γ (memberGraph ids k)) →
    Nonempty (Derivation body Γ (memberGraph args l)) →
    Nonempty (Derivation body Γ (memberGraph args r)) →
    Nonempty (Derivation body Γ (memberGraph out (numberedTerm h ty k l r)))

structure BoundedNumberedArgs (body : Positive (Fin 1)) {α : Type} (Γ : List (Formula α))
    (d H K M da Ma state terms args key : OTerm α) : Prop where
  scope : Nonempty (Derivation body Γ (observed da H K Ma state terms args))
  hit : Nonempty (Derivation body Γ (memberGraph args key))
  depth : Nonempty (Derivation body Γ (ltF da (suc d)))
  width : Nonempty (Derivation body Γ (ltF Ma (suc M)))

def ExactOpenSelectedGrammarNumberedFromPredecessor : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (d H K M prev prevTerms prevArgs next out nextArgs h ty k l r : OTerm α),
    Nonempty (Derivation body Γ (observed d H K M prev prevTerms prevArgs)) →
    Nonempty (Derivation body Γ (observed (suc d) H K M next out nextArgs)) →
    Nonempty (Derivation body Γ (memberGraph H h)) →
    Nonempty (Derivation body Γ (memberGraph K ty)) →
    Nonempty (Derivation body Γ (ltF k (suc M))) →
    Nonempty (Derivation body Γ (memberGraph prevArgs l)) →
    Nonempty (Derivation body Γ (memberGraph prevArgs r)) →
    Nonempty (Derivation body Γ (memberGraph out (numberedTerm h ty k l r)))

def ExactOpenSelectedGrammarNumberedAtBounds : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (d H K M dl Ml lState lTerms lArgs dr Mr rState rTerms rArgs
      prev prevTerms prevArgs next out nextArgs h ty k l r : OTerm α),
    BoundedNumberedArgs body Γ d H K M dl Ml lState lTerms lArgs l →
    BoundedNumberedArgs body Γ d H K M dr Mr rState rTerms rArgs r →
    Nonempty (Derivation body Γ (observed d H K M prev prevTerms prevArgs)) →
    Nonempty (Derivation body Γ (observed (suc d) H K M next out nextArgs)) →
    Nonempty (Derivation body Γ (memberGraph H h)) →
    Nonempty (Derivation body Γ (memberGraph K ty)) →
    Nonempty (Derivation body Γ (ltF k (suc M))) →
    Nonempty (Derivation body Γ (memberGraph out (numberedTerm h ty k l r)))

/-- Genuine two argument scopes and actual numbered parent reports, not
an assertion of what the numbered evaluator accepts or returns. -/
structure NumberedOwnInputs (V Measure : Program 1) (s : Settings)
    (body : Positive (Fin 1)) {α : Type} (Γ : List (Formula α))
    (m d M dl Ml lState lTerms lArgs dr Mr rState rTerms rArgs h ty k l r : OTerm α) : Prop where
  prefix : BoundedNumberedArgs body Γ d (headsTerm s α) (typesTerm s α) M dl Ml lState lTerms lArgs l
  suffix : BoundedNumberedArgs body Γ d (headsTerm s α) (typesTerm s α) M dr Mr rState rTerms rArgs r
  headHit : Nonempty (Derivation body Γ (memberGraph (headsTerm s α) h))
  typeHit : Nonempty (Derivation body Γ (memberGraph (typesTerm s α) ty))
  idBound : Nonempty (Derivation body Γ (ltF k (suc M)))
  validity : Nonempty (Derivation body Γ (unary V (suc z) (numberedTerm h ty k l r)))
  measurement : Nonempty (Derivation body Γ (unary Measure m (numberedTerm h ty k l r)))
  parentPair : Nonempty (Derivation body Γ (measurePair m d M))

def ExactOpenSelectedGrammarNumberedScratch : Prop :=
  ∀ (V Measure : Program 1) (s : Settings) (body : Positive (Fin 1)) (α : Type)
    (Γ : List (Formula α))
    (m d M dl Ml lState lTerms lArgs dr Mr rState rTerms rArgs vertices h ty k l r : OTerm α),
    NumberedOwnInputs V Measure s body Γ m d M dl Ml lState lTerms lArgs dr Mr rState rTerms rArgs h ty k l r →
    Nonempty (Derivation body Γ
      (unary (scratchVertices (selectedCover V Measure) s) vertices (numberedTerm h ty k l r))) →
    Nonempty (Derivation body Γ (memberGraph vertices (numberedTerm h ty k l r)))

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarNumberedOwnTargets
