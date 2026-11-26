module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarAuxScratchTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarNullaryTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary)
open NumberedWindowInternalSparseCoverScratch (scratchVertices)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalCoverOrdinaryLayerTargets (taggedTerm)
open NumberedWindowInternalFactoredAuxOwnCoverTargets (headsTerm measurePair)
open NumberedWindowInternalCoverSelectedSuccessorTargets (stepReport)
open NumberedWindowInternalCoverSelectedGrammarWidthTargets (observed)
open NumberedWindowInternalCoverSelectedGrammarAuxScratchTargets (selectedCover)

/-- Literal original ordinary head with the empty sparse argument list,
not a standalone or numbered-head grammar tag. -/
abbrev nullaryKey {α : Type} (h : OTerm α) := taggedTerm 4 h z

def OpenSelectedPartContainsNullary (P : Program 5) : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (out H K ids terms args h : OTerm α),
    Nonempty (Derivation body Γ (stepReport P out H K ids terms args)) →
    Nonempty (Derivation body Γ (memberGraph H h)) →
    Nonempty (Derivation body Γ (memberGraph args z)) →
    Nonempty (Derivation body Γ (memberGraph out (nullaryKey h)))

/-- The actual chosen args output at any genuine observed depth
contains the original zero seed. -/
def ExactOpenSelectedGrammarEmptyArgs : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (d H K width state terms args : OTerm α),
    Nonempty (Derivation body Γ (observed d H K width state terms args)) →
    Nonempty (Derivation body Γ (memberGraph args z))

def ExactOpenSelectedGrammarNullaryAtSuccessor : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (d H K width next out args h : OTerm α),
    Nonempty (Derivation body Γ (observed (suc d) H K width next out args)) →
    Nonempty (Derivation body Γ (memberGraph H h)) →
    Nonempty (Derivation body Γ (memberGraph out (nullaryKey h)))

def ExactOpenSelectedGrammarNullaryScratch : Prop :=
  ∀ (V Measure : Program 1) (s : Settings) (body : Positive (Fin 1)) (α : Type)
    (Γ : List (Formula α)) (m d width vertices h : OTerm α),
    Nonempty (Derivation body Γ (memberGraph (headsTerm s α) h)) →
    Nonempty (Derivation body Γ (unary V (suc z) (nullaryKey h))) →
    Nonempty (Derivation body Γ (unary Measure m (nullaryKey h))) →
    Nonempty (Derivation body Γ (measurePair m d width)) →
    Nonempty (Derivation body Γ
      (unary (scratchVertices (selectedCover V Measure) s) vertices (nullaryKey h))) →
    Nonempty (Derivation body Γ (memberGraph vertices (nullaryKey h)))

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarNullaryTargets
