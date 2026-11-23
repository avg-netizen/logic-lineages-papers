module
public import LogicLineages.PersistentMarking.NumberedWindowTypeApplicationRuleTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAccessibilityRulesTargets
import LogicLineages.PersistentMarking.NumberedWindowTypeApplicationRuleChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceIntroductionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalRankedNeutralTypeProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators
open LogicLineages.OrdinalComparison.Source (Ty)
open ID1Completion.InternalCalculus ID1Completion.InternalAccessibilityRules
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalSourceIntroductionSyntaxProof (formulaRelabelAsSubst termRelabelAsSubst)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb sucRelabel)
open ID1Completion.SourcePresentation (Data sourceBody)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowComputabilityFormulaTargets (formula accepts)
open NumberedWindowTypeApplicationRuleChecks (exact_FormulaSubstitution exact_ApplicationIntroduction)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary suc)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)

/-- A true rank report is an open use of the actual physical g. The zero
output of g need not denote any member. -/
def RankedNeutralGround (S : Data) (g : Program 1) (c : Nat) : Prop :=
  ∀ (α : Type) (Γ : List (Formula α)) (k q : OTerm α),
    Nonempty (Derivation (sourceBody S c) Γ (unary g (suc k) q)) →
    Nonempty (Derivation (sourceBody S c) Γ (carrier S false c q)) →
    Nonempty (Derivation (sourceBody S c) Γ (membership false q))

/-- Only actual arithmetic images: an accepted application of a
positive-rank function has a real positive-rank report and carrier at its
same given output y. No computation or C predicate is a premise. -/
def RankedNeutralApplication (S : Data) (g : Program 1) (p : Program 3) (c : Nat) : Prop :=
  ∀ (α : Type) (Γ : List (Formula α)) (k f u y : OTerm α) (goal : Formula α),
    Nonempty (Derivation (sourceBody S c) Γ (unary g (suc k) f)) →
    Nonempty (Derivation (sourceBody S c) Γ (accepts p f u y)) →
    (∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (m : OTerm β),
      (∀ q ∈ Γ, q.relabel j ∈ Δ) →
      Nonempty (Derivation (sourceBody S c) Δ (unary g (suc m) (y.relabel j))) →
      Nonempty (Derivation (sourceBody S c) Δ (carrier S false c (y.relabel j))) →
      Nonempty (Derivation (sourceBody S c) Δ (goal.relabel j))) →
    Nonempty (Derivation (sourceBody S c) Γ goal)

private theorem renameC {α β : Type} (p : Program 3) (τ : Ty) (q : OTerm α) (j : α → β) :
    (formula p τ q).relabel j = formula p τ (q.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (formula p τ q).subst (fun x => emb (.var (j x))) = _
  rw [exact_FormulaSubstitution p τ α β q _, ← termRelabelAsSubst]

/-- The finite-type recursion (T) has no remaining domain restriction
once those two true arithmetic rules hold in the same original body.
The introduced domain C hypothesis is still present; the neutral
arithmetic reports do not depend on it. -/
theorem exact_RankedNeutralComputability (S : Data) (g : Program 1) (p : Program 3) (c : Nat)
    (base : RankedNeutralGround S g c) (applies : RankedNeutralApplication S g p c) :
    ∀ (τ : Ty) (α : Type) (Γ : List (Formula α)) (k q : OTerm α),
      Nonempty (Derivation (sourceBody S c) Γ (unary g (suc k) q)) →
      Nonempty (Derivation (sourceBody S c) Γ (carrier S false c q)) →
      Nonempty (Derivation (sourceBody S c) Γ (formula p τ q)) := by
  let B := sourceBody S c
  intro τ
  induction τ with
  | ground =>
    exact base
  | arrow σ τ _ ih =>
    intro α Γ k f ranked _
    apply exact_ApplicationIntroduction B p σ τ α Γ f
    let β := (α ⊕ Fin 1) ⊕ Fin 1
    let j : α → β := fun x => .inl (.inl x)
    let u : OTerm β := .var (.inl (.inr 0))
    let y : OTerm β := .var (.inr 0)
    let A := formula p σ u
    let E := accepts p (f.relabel j) u y
    let Δ := A :: E :: (Γ.map weaken).map weaken
    change Nonempty (Derivation B Δ (formula p τ y))
    have keep (a : Formula α) (ha : a ∈ Γ) : a.relabel j ∈ Δ := by
      apply List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ?_)
      refine List.mem_map.mpr ⟨a.relabel Sum.inl,List.mem_map.mpr ⟨a,ha,rfl⟩,?_⟩
      exact formulaRelabelComposition (Sum.inl : α → α ⊕ Fin 1) (Sum.inl : α ⊕ Fin 1 → β) a
    have r := renameInto ranked j Δ keep
    rw [unaryRename,sucRelabel] at r
    have a : Nonempty (Derivation B Δ E) := ⟨Derivation.hypothesis
      (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    apply applies β Δ (k.relabel j) (f.relabel j) u y (formula p τ y) r a
    intro γ j' Θ m _ result held
    rw [renameC]
    exact ih γ Θ m (y.relabel j') result held

#print axioms exact_RankedNeutralComputability
end LogicLineages.PersistentMarking.NumberedWindowInternalRankedNeutralTypeProof
