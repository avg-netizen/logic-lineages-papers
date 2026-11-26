module

public import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralFactsSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalPullbackSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.InverseApplicationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralFirstHopProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalNeutralFactsProof
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

private theorem atoms (rules : Arithmetic S p h n b v c) (τ : Ty)
    (neutral : ∀ (α : Type) (Γ : List (Formula α)) (x : OTerm α),
      D S c Γ (carrier S false c x) → D S c Γ (atom n x) →
      D S c Γ (reducts S p h c τ x) → D S c Γ (formula p τ x)) :
    FactsAt S p h n b v c τ := by
  have bottom (α : Type) (Γ : List (Formula α)) (x : OTerm α)
      (typed : D S c Γ (carrier S false c x)) (held : D S c Γ (atom b x)) :
      D S c Γ (formula p τ x) := by
    apply neutral α Γ x typed (rules.bottomNeutral α Γ x held)
    apply reductsIntro S p h c τ x
    intro β j Δ y keeps path
    have shape := renameInto held j Δ keeps
    rw [atomRename] at shape
    obtain ⟨no⟩ := rules.bottomNoStep β Δ (x.relabel j) y shape path
    exact ⟨Derivation.explosion no⟩
  refine ⟨neutral,bottom,?_⟩
  intro α Γ x typed held
  apply neutral α Γ x typed (rules.variableNeutral α Γ x held)
  apply reductsIntro S p h c τ x
  intro β j Δ y keeps path
  have shape := renameInto held j Δ keeps
  rw [atomRename] at shape
  exact bottom β Δ y (rules.directCarrier β Δ (x.relabel j) y path)
    (rules.variableStep β Δ (x.relabel j) y shape path)

private theorem usingInherited (σ τ : Ty) {α : Type} {Γ : List (Formula α)}
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

private theorem openedInversion (rules : Arithmetic S p h n b v c) (σ τ : Ty)
    (atTarget : FactsAt S p h n b v c τ)
    {α : Type} {Γ : List (Formula α)} (x u t y : OTerm α)
    (neutral : D S c Γ (atom n x)) (app : D S c Γ (accepts p x u t))
    (step : D S c Γ (direct S h c t y))
    (earlier : D S c Γ (reducts S p h c (.arrow σ τ) x))
    (input : D S c Γ (formula p σ u)) :
    D S c Γ (formula p τ y) := by
  have types := rules.directCarrier α Γ t y step
  let Btm := atom b y
  let Other := inherited S p h c x u y
  have add {f : Formula α} (A : Formula α) (h : D S c Γ f) : D S c (A :: Γ) f :=
    h.map (Derivation.weakening (fun _ hp => List.mem_cons_of_mem _ hp))
  obtain ⟨one⟩ := atTarget.bottom α (Btm :: Γ) y (add Btm types) ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨two⟩ := usingInherited σ τ x u y (add Other earlier) (add Other input)
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨split⟩ := rules.applicationInversion α Γ x u t y neutral app step
  exact ⟨disjunctionElimination split (Derivation.implicationIntroduction one)
    (Derivation.implicationIntroduction two)⟩

private theorem arrow (rules : Arithmetic S p h n b v c) (σ τ : Ty)
    (atTarget : FactsAt S p h n b v c τ)
    (α : Type) (Γ : List (Formula α)) (x : OTerm α)
    (neutral : D S c Γ (atom n x)) (earlier : D S c Γ (reducts S p h c (.arrow σ τ) x)) :
    D S c Γ (formula p (.arrow σ τ) x) := by
  apply exact_ApplicationIntroduction (sourceBody S c) p σ τ α Γ x
  let j₁ : α → α ⊕ Fin 1 := Sum.inl
  let j₂ : α ⊕ Fin 1 → (α ⊕ Fin 1) ⊕ Fin 1 := Sum.inl
  let j : α → (α ⊕ Fin 1) ⊕ Fin 1 := j₂ ∘ j₁
  let u : OTerm ((α ⊕ Fin 1) ⊕ Fin 1) := .var (.inl (.inr 0))
  let t : OTerm ((α ⊕ Fin 1) ⊕ Fin 1) := .var (.inr 0)
  let x' := x.relabel j
  let A := accepts p x' u t
  let C := formula p σ u
  let Δ := C :: A :: (Γ.map weaken).map weaken
  change D S c Δ (formula p τ t)
  have keep (f : Formula α) (h : f ∈ Γ) : f.relabel j ∈ Δ := by
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    rw [← formulaRelabelComposition j₁ j₂]
    apply List.mem_map.mpr
    exact ⟨weaken f,List.mem_map.mpr ⟨f,h,rfl⟩,rfl⟩
  have nn := renameInto neutral j Δ keep
  rw [atomRename] at nn
  have ee := renameInto earlier j Δ keep
  rw [reductsRename] at ee
  have app : D S c Δ A := ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  have input : D S c Δ C := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨typedT,neutralT⟩ := rules.applicationNeutral _ Δ x' u t nn app
  apply atTarget.neutral _ Δ t typedT neutralT
  apply reductsIntro S p h c τ t
  intro β k Ω y retain strict
  have a := renameInto app k Ω retain
  change D S c Ω ((accepts p x' u t).relabel k) at a
  rw [acceptsRename] at a
  have nu := renameInto nn k Ω retain
  rw [atomRename] at nu
  have older := renameInto ee k Ω retain
  rw [reductsRename] at older
  have supply := renameInto input k Ω retain
  change D S c Ω ((formula p σ u).relabel k) at supply
  rw [formulaRename] at supply
  exact openedInversion rules σ τ atTarget (x'.relabel k) (u.relabel k) (t.relabel k)
    y nu a strict older supply

/-- The simultaneous internal neutral, bottom and variable argument
uses the literal manuscript computability formulas and actual ID₁
rules. The arithmetic inversion and atomic shape rules are still
explicit hypotheses, not silently assumed from numerical correctness. -/
theorem exact_ConditionalInternalNeutralFacts (rules : Arithmetic S p h n b v c) (τ : Ty) :
    FactsAt S p h n b v c τ := by
  induction τ with
  | ground =>
    apply atoms rules
    intro α Γ x carrier _ all
    apply membershipIntroduction S c x carrier
    intro β j Δ y keep e
    have earlier := renameInto all j Δ keep
    rw [reductsRename] at earlier
    exact firstHopGround S p h c (x.relabel j) y earlier (rules.pathFirstHop β Δ (x.relabel j) y e)
  | arrow σ τ _ target =>
    apply atoms rules
    intro α Γ x _ hg lower
    exact arrow rules σ τ target α Γ x hg lower

#print axioms exact_ConditionalInternalNeutralFacts
end LogicLineages.PersistentMarking.NumberedWindowInternalNeutralFactsProof
