module
public import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralFactsProof

public import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralFactsSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalPullbackSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.InverseApplicationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralFirstHopProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralApplicationReductComputabilityProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open LogicLineages.OrdinalComparison.Source (Ty)
open PositiveArithmeticOperators SourceComputabilityFormulaSupportProof
open ID1Completion.InternalCalculus ID1Completion.InternalAccessibilityRules
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.SourcePresentation (Data sourceBody)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open ID1Completion.InternalBetaTotalityProof (disjunctionElimination)
open ID1Completion.SourceComputabilityCompletion.InverseApplicationProof (membershipIntroduction)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowComputabilityFormulaTargets (accepts formula)
open NumberedWindowTypeApplicationRuleChecks (exact_ApplicationIntroduction exact_ApplicationElimination)
open NumberedWindowInternalPullbackSyntaxProof (acceptsRename)
open NumberedWindowInternalNeutralFactsTargets
open NumberedWindowInternalNeutralFactsSyntaxProof
open NumberedWindowInternalNeutralFirstHopProof (firstHopGround)

variable {S : Data} {p h : Program 3} {n b v : Program 1} {c : Nat}

theorem exact_OpenInheritedApplicationComputable (σ τ : Ty) {α : Type} {Γ : List (Formula α)}
    (x u y : OTerm α)
    (earlier : D S c Γ (reducts S p h c (.arrow σ τ) x))
    (input : D S c Γ (formula p σ u))
    (held : D S c Γ (inherited S p h c x u y)) : D S c Γ (formula p τ y) := by
  let j : α → α ⊕ Fin 1 := Sum.inl
  let q : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let A := direct S h c (x.relabel j) q ⊓ accepts p q (u.relabel j) (y.relabel j)
  let Δ : List (Formula (α ⊕ Fin 1)) := A :: Γ.map weaken
  have keep (f : Formula α) (h : f ∈ Γ) : f.relabel j ∈ Δ :=
    List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,h,rfl⟩)
  have steps := renameInto earlier j Δ keep
  rw [reductsRename] at steps
  have arg := renameInto input j Δ keep
  rw [formulaRename] at arg
  have pair : Derivation (sourceBody S c) Δ A := Derivation.hypothesis List.mem_cons_self
  have f := reductAt S p h c (.arrow σ τ) (x.relabel j) q steps ⟨Derivation.conjunctionLeft pair⟩
  obtain ⟨out⟩ := exact_ApplicationElimination (sourceBody S c) p σ τ _ Δ q (u.relabel j) (y.relabel j)
    f ⟨Derivation.conjunctionRight pair⟩ arg
  have actual : Derivation (sourceBody S c) Δ (weaken (formula p τ y)) := by
    rw [weaken,formulaRename]
    exact out
  obtain ⟨earlierApp⟩ := held
  exact ⟨Derivation.existentialElimination earlierApp actual⟩


/-- Precise beta, bottom and inherited classification suffices for
computability of an actual direct application reduct. The beta proof
is already an object-language derivation at this exact target. -/
theorem exact_OpenComputableApplicationReduct (rules : Arithmetic S p h n b v c) (σ τ : Ty)
    (atTarget : FactsAt S p h n b v c τ)
    {α : Type} {Γ : List (Formula α)} (x u t y : OTerm α)
    (step : D S c Γ (direct S h c t y))
    (earlier : D S c Γ (reducts S p h c (.arrow σ τ) x))
    (input : D S c Γ (formula p σ u))
    (split : D S c Γ (atom b y ⊔ (inherited S p h c x u y ⊔ formula p τ y))) :
    D S c Γ (formula p τ y) := by
  have held := rules.directCarrier α Γ t y step
  let bb := atom b y
  let rr := inherited S p h c x u y
  let ff := formula p τ y
  let rest := rr ⊔ ff
  have add {Δ : List (Formula α)} {f : Formula α} (A : Formula α) (h : D S c Δ f) : D S c (A :: Δ) f :=
    h.map (Derivation.weakening (fun _ hp => List.mem_cons_of_mem _ hp))
  obtain ⟨base⟩ := atTarget.bottom α (bb :: Γ) y (add bb held) ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨carry⟩ := exact_OpenInheritedApplicationComputable σ τ x u y
    (add rr (add rest earlier)) (add rr (add rest input)) ⟨Derivation.hypothesis List.mem_cons_self⟩
  have calcRest : Derivation (sourceBody S c) (rest :: Γ) ff :=
    disjunctionElimination (Derivation.hypothesis List.mem_cons_self)
      (Derivation.implicationIntroduction carry) (Derivation.implicationIntroduction (Derivation.hypothesis List.mem_cons_self))
  obtain ⟨split⟩ := split
  exact ⟨disjunctionElimination split (Derivation.implicationIntroduction base)
    (Derivation.implicationIntroduction calcRest)⟩

#print axioms exact_OpenInheritedApplicationComputable
#print axioms exact_OpenComputableApplicationReduct
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralApplicationReductComputabilityProof
