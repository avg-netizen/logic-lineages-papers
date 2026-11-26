module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralJoinedBetaOutcomeProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralApplicationReductComputabilityProof
import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralFactsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralInheritedApplicationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalPullbackSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralFactsSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBetaApplicationComputabilityProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open LogicLineages.OrdinalComparison.Source (Ty)
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAccessibilityRules (carrier)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.SourcePresentation (Data sourceBody)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowComputabilityFormulaTargets (accepts formula)
open NumberedWindowInternalNeutralFactsTargets (D Arithmetic FactsAt atom direct inherited reducts)
open NumberedWindowInternalNeutralFactsSyntaxProof (formulaRename reductsRename reductsIntro)
open NumberedWindowInternalNeutralFactsProof (exact_ConditionalInternalNeutralFacts)
open NumberedWindowInternalPullbackSyntaxProof (acceptsRename)
open NumberedWindowInternalLiteralJoinedBetaOutcomeProof (BetaOutcomeAt)
open NumberedWindowInternalLiteralApplicationReductComputabilityProof (exact_OpenComputableApplicationReduct)

/-- This is the actual open three-way application rule, not an
assumption that the abstraction or its beta instance is computable. -/
def BetaApplicationCases (data : Data) (p h L₀ L : Program 3) (i bottom : Program 1)
    (U : Program 2) (c : Nat) : Prop :=
  ∀ (α : Type) (Γ : List (Formula α)) (x u t y : OTerm α) (goal : Formula α),
    D data c Γ (accepts p x u t) → D data c Γ (direct data h c t y) →
    BetaOutcomeAt (sourceBody data c) Γ i L₀ L U x u y goal →
    D data c Γ (atom bottom y ⊔ (inherited data p h c x u y ⊔ goal))

def ApplicationOutput (data : Data) (p : Program 3) (n : Program 1) (c : Nat) : Prop :=
  ∀ (α : Type) (Γ : List (Formula α)) (x u t : OTerm α),
    D data c Γ (accepts p x u t) →
    D data c Γ (carrier data false c t) ∧ D data c Γ (atom n t)

/-- The actual accepted application is computable provided its real
aligned beta outcomes are computable, the unchanged argument
computes, and all proper direct function reducts compute. The
recursive use of the neutral lemma is at the genuine output type. -/
theorem exact_OpenApplicationComputabilityFromBeta
    (data : Data) (p h L₀ L : Program 3) (i n b v : Program 1) (U : Program 2) (c : Nat)
    (rules : Arithmetic data p h n b v c) (out : ApplicationOutput data p n c)
    (cases : BetaApplicationCases data p h L₀ L i b U c) (σ τ : Ty)
    {α : Type} {Γ : List (Formula α)} (x u t : OTerm α)
    (app : D data c Γ (accepts p x u t))
    (earlier : D data c Γ (reducts data p h c (.arrow σ τ) x))
    (arg : D data c Γ (formula p σ u))
    (beta : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (y : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      D data c Δ (direct data h c (t.relabel j) y) →
      BetaOutcomeAt (sourceBody data c) Δ i L₀ L U (x.relabel j) (u.relabel j) y (formula p τ y)) :
    D data c Γ (formula p τ t) := by
  have facts := exact_ConditionalInternalNeutralFacts rules τ
  obtain ⟨typed,neutral⟩ := out α Γ x u t app
  apply facts.neutral α Γ t typed neutral
  apply reductsIntro data p h c τ t
  intro β j Δ y keep step
  have app' := renameInto app j Δ keep
  rw [acceptsRename] at app'
  have earlier' := renameInto earlier j Δ keep
  rw [reductsRename] at earlier'
  have arg' := renameInto arg j Δ keep
  rw [formulaRename] at arg'
  have split := cases β Δ (x.relabel j) (u.relabel j) (t.relabel j) y (formula p τ y)
    app' step (beta β j Δ y keep step)
  exact exact_OpenComputableApplicationReduct rules σ τ facts (x.relabel j) (u.relabel j) (t.relabel j)
    y step earlier' arg' split

#print axioms BetaApplicationCases
#print axioms ApplicationOutput
#print axioms exact_OpenApplicationComputabilityFromBeta
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBetaApplicationComputabilityProof
