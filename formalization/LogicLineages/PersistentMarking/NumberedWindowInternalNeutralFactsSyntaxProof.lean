module

public import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralFactsTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalPullbackSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAccessibilityRulesSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityApplicationSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceIntroductionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalNeutralFactsSyntaxProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open LogicLineages.OrdinalComparison.Source (Ty)
open PositiveArithmeticOperators SourceComputabilityFormulaSupportProof
open ID1Completion.InternalCalculus ID1Completion.InternalAccessibilityRules ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.SourcePresentation (Data sourceBody)
open ID1Completion.InternalTagArithmeticSyntaxProof
  (emb bindEmbedding liftBind varBind sucRelabel zRelabel)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalAccessibilityRulesSyntaxProof (edgeSubst)
open ID1Completion.InternalComputabilityApplicationSyntaxProof (allEmbeddedSubst liftTermSubst)
open ID1Completion.InternalSourceIntroductionSyntaxProof (formulaRelabelAsSubst termRelabelAsSubst)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowComputabilityFormulaTargets (formula)
open NumberedWindowTypeApplicationRuleChecks (exact_FormulaSubstitution)
open NumberedWindowTypeFormulaSubstitutionProof (impSubst)
open NumberedWindowInternalNeutralFactsTargets

private theorem formulaSubst {α β : Type} (p : Program 3) (τ : Ty) (x : OTerm α)
    (ts : α → OTerm β) :
    (formula p τ x).subst (fun k => emb (ts k)) = formula p τ (x.subst ts) :=
  exact_FormulaSubstitution p τ α β x ts

theorem formulaRename {α β : Type} (p : Program 3) (τ : Ty) (x : OTerm α) (j : α → β) :
    (formula p τ x).relabel j = formula p τ (x.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (formula p τ x).subst (fun a => emb (.var (j a))) = _
  rw [exact_FormulaSubstitution p τ α β x _,← termRelabelAsSubst]

theorem atomRename {α β : Type} (test : Program 1) (x : OTerm α) (j : α → β) :
    (atom test x).relabel j = atom test (x.relabel j) := by
  unfold atom
  rw [programRename,sucRelabel,zRelabel]
  congr 1
  funext k
  obtain rfl := Fin.eq_zero k
  rfl

theorem reductsRename {α β : Type} (S : Data) (p h : Program 3) (c : Nat) (τ : Ty)
    (x : OTerm α) (j : α → β) :
    (reducts S p h c τ x).relabel j = reducts S p h c τ (x.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (reducts S p h c τ x).subst (fun a => emb (.var (j a))) = _
  simp only [reducts,direct,allEmbeddedSubst,impSubst,edgeSubst,formulaSubst,liftTermSubst,
    termRelabelAsSubst x j]
  rfl

theorem reductAt (S : Data) (p h : Program 3) (c : Nat) (τ : Ty)
    {α : Type} {Γ : List (Formula α)} (x y : OTerm α)
    (all : D S c Γ (reducts S p h c τ x)) (one : D S c Γ (direct S h c x y)) :
    D S c Γ (formula p τ y) := by
  obtain ⟨proof⟩ := all
  obtain ⟨e⟩ := one
  rw [reducts,direct] at proof
  have inst := Derivation.universalElimination (emb y) proof
  simp only [instantiate,bindEmbedding,impSubst,edgeSubst,formulaSubst,liftBind,varBind] at inst
  exact ⟨Derivation.implicationElimination inst e⟩

theorem reductsIntro (S : Data) (p h : Program 3) (c : Nat) (τ : Ty)
    {α : Type} {Γ : List (Formula α)} (x : OTerm α)
    (next : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (y : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) → D S c Δ (direct S h c (x.relabel j) y) →
      D S c Δ (formula p τ y)) :
    D S c Γ (reducts S p h c τ x) := by
  let j : α → α ⊕ Fin 1 := Sum.inl
  let y : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let A := direct S h c (x.relabel j) y
  let Δ := A :: Γ.map weaken
  obtain ⟨out⟩ := next (α ⊕ Fin 1) j Δ y
    (fun f h => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,h,rfl⟩))
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.universalIntroduction (Derivation.implicationIntroduction out)⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalNeutralFactsSyntaxProof
