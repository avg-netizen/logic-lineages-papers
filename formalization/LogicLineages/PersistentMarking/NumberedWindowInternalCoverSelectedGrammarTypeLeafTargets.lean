module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarAuxScratchTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarTypeLeafTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary)
open NumberedWindowInternalSparseCoverScratch (scratchVertices)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalCoverTypeLeavesTargets (typeLeafTerm)
open NumberedWindowInternalFactoredAuxOwnCoverTargets (typesTerm measurePair)
open NumberedWindowInternalCoverSelectedSuccessorTargets (stepReport)
open NumberedWindowInternalCoverSelectedGrammarWidthTargets (observed)
open NumberedWindowInternalCoverSelectedGrammarAuxScratchTargets (selectedCover)

def OpenSelectedPartContainsTypeLeaf (P : Program 5) : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (out H K ids terms args ty : OTerm α),
    Nonempty (Derivation body Γ (stepReport P out H K ids terms args)) →
    Nonempty (Derivation body Γ (memberGraph K ty)) →
    Nonempty (Derivation body Γ (memberGraph out (typeLeafTerm ty)))

/-- An actual successor observation contains the original type-only
leaf if its type occurs on the literal type axis. No child term or
numeral-index premise is needed. -/
def ExactOpenSelectedGrammarTypeLeafAtSuccessor : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (d H K width next out args ty : OTerm α),
    Nonempty (Derivation body Γ (observed (suc d) H K width next out args)) →
    Nonempty (Derivation body Γ (memberGraph K ty)) →
    Nonempty (Derivation body Γ (memberGraph out (typeLeafTerm ty)))

/-- Same physical scratch and original type-only key, when the
actual measure reports a successor depth and admits this type and key. -/
def ExactOpenSelectedGrammarTypeLeafScratch : Prop :=
  ∀ (V Measure : Program 1) (s : Settings) (body : Positive (Fin 1)) (α : Type)
    (Γ : List (Formula α)) (m d width vertices ty : OTerm α),
    Nonempty (Derivation body Γ (memberGraph (typesTerm s α) ty)) →
    Nonempty (Derivation body Γ (unary V (suc z) (typeLeafTerm ty))) →
    Nonempty (Derivation body Γ (unary Measure m (typeLeafTerm ty))) →
    Nonempty (Derivation body Γ (measurePair m d width)) →
    Nonempty (Derivation body Γ (unary (scratchVertices (selectedCover V Measure) s) vertices (typeLeafTerm ty))) →
    Nonempty (Derivation body Γ (memberGraph vertices (typeLeafTerm ty)))

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarTypeLeafTargets
