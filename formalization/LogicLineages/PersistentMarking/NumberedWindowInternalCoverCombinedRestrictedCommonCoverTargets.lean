module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarOptionTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverScratchOpenTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedCommonCoverTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc z)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparseCoverScratch (coverOption)
open NumberedWindowInternalAuxMeasureMemoTargets (selectedMeasure)
open NumberedWindowInternalCoverSelectedGrammarAuxScratchTargets (selectedCover)
open NumberedWindowInternalCoverCombinedRestrictedTargets (combinedPrograms)

/-- Actual common-output continuation. The result is one successful
original Option value, at the two distinct physical seed tapes. -/
def CommonCoverK {α : Type} (C : Program 3) (s : Settings) (body : Positive (Fin 1))
    (Γ : List (Formula α)) (a b : OTerm α) (goal : Formula α) : Prop :=
  ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (vertices : OTerm β),
    (∀ p ∈ Γ, p.relabel j ∈ Δ) →
    Nonempty (Derivation body Δ (unary (coverOption C s) (suc vertices) (a.relabel j))) →
    Nonempty (Derivation body Δ (unary (coverOption C s) (suc vertices) (b.relabel j))) →
    Nonempty (Derivation body Δ (goal.relabel j))

def ExactOpenCoverCommonSelectedCover : Prop :=
  ∀ (V N : Program 1) (s : Settings) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (a b m : OTerm α) (goal : Formula α),
    Nonempty (Derivation body Γ (unary V (suc z) a)) →
    Nonempty (Derivation body Γ (unary V (suc z) b)) →
    Nonempty (Derivation body Γ (unary N m a)) →
    Nonempty (Derivation body Γ (unary N m b)) →
    CommonCoverK (selectedCover V N) s body Γ a b goal →
    Nonempty (Derivation body Γ goal)

def ExactOpenCoverCombinedRestrictedCommonCover : Prop :=
  ∀ (V TV M M0 : Program 1) (B : Program 2) (T : Program 1) (s : Settings)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (a b m : OTerm α) (goal : Formula α),
    let P := combinedPrograms s V TV M M0 B T
    Nonempty (Derivation body Γ (unary P.V (suc z) a)) →
    Nonempty (Derivation body Γ (unary P.V (suc z) b)) →
    Nonempty (Derivation body Γ (unary (selectedMeasure P.R) m a)) →
    Nonempty (Derivation body Γ (unary (selectedMeasure P.R) m b)) →
    CommonCoverK P.cover s body Γ a b goal →
    Nonempty (Derivation body Γ goal)

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedCommonCoverTargets
