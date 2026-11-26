module

public import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralFactsSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicMembershipSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAccessibilityRulesProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAccessibilityRulesSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalNeutralFirstHopProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalAccessibilityRules
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn emb bindEmbedding varBind)
open ID1Completion.InternalAccessibilityRulesSyntaxProof (membershipSubst)
open ID1Completion.InternalAccessibilityRulesProof (actualOriginalSuccessorClosure)
open ID1Completion.InternalBetaTotalityProof (disjunctionElimination)
open ID1Completion.SourcePresentation (Data sourceBody)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowComputabilityFormulaTargets (formula)
open NumberedWindowInternalNeutralFactsTargets
open NumberedWindowInternalNeutralFactsSyntaxProof (reductsRename reductAt)
open NumberedWindowInternalAtomicMembershipSyntaxProof (membershipRename)

private theorem equalityPreservesI (S : Data) (c : Nat)
    {α : Type} {Γ : List (Formula α)} (x y : OTerm α)
    (e : D S c Γ (eqn x y)) (ix : D S c Γ (membership false x)) :
    D S c Γ (membership false y) := by
  let θ : Formula (α ⊕ Fin 1) := membership false (.var (.inr 0))
  have atValue (w : OTerm α) : instantiate θ (emb w) = membership false w := by
    simp only [θ,instantiate,bindEmbedding,membershipSubst,varBind]
  obtain ⟨eq⟩ := e
  obtain ⟨before⟩ := ix
  have held : Derivation (sourceBody S c) Γ (instantiate θ (emb x)) := by
    rw [atValue]
    exact before
  have out := Derivation.equalityElimination θ (emb x) (emb y) eq held
  rw [atValue] at out
  exact ⟨out⟩

/-- For the ground case, the first actual direct reduct is in I by the
held reducts formula. A positive continuation uses downward closure;
an identical endpoint uses only object equality. -/
theorem firstHopGround (S : Data) (p h : Program 3) (c : Nat)
    {α : Type} {Γ : List (Formula α)} (x y : OTerm α)
    (all : D S c Γ (reducts S p h c .ground x))
    (hop : D S c Γ (firstHop S h c x y)) : D S c Γ (membership false y) := by
  let j : α → α ⊕ Fin 1 := Sum.inl
  let w : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let B := sourceBody S c
  let E := eqn w (y.relabel j)
  let R := edge S false c w (y.relabel j)
  let A := direct S h c (x.relabel j) w ⊓ (E ⊔ R)
  let Δ : List (Formula (α ⊕ Fin 1)) := A :: Γ.map weaken
  have keep (f : Formula α) (mem : f ∈ Γ) : f.relabel j ∈ Δ :=
    List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,mem,rfl⟩)
  have moved := renameInto all j Δ keep
  rw [reductsRename] at moved
  have facts : Derivation B Δ A := Derivation.hypothesis List.mem_cons_self
  have first : D S c Δ (membership false w) :=
    reductAt S p h c .ground (x.relabel j) w moved ⟨Derivation.conjunctionLeft facts⟩
  have add (F : Formula (α ⊕ Fin 1)) : D S c (F :: Δ) (membership false w) :=
    first.map (Derivation.weakening (fun _ mem => List.mem_cons_of_mem _ mem))
  obtain ⟨eq⟩ := equalityPreservesI S c w (y.relabel j)
    (⟨Derivation.hypothesis List.mem_cons_self⟩ : D S c (E :: Δ) E) (add E)
  obtain ⟨next⟩ := actualOriginalSuccessorClosure S false c _ (R :: Δ) w (y.relabel j) (add R)
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have forward : Derivation B Δ (weaken (membership false y)) := by
    rw [weaken,membershipRename]
    exact disjunctionElimination (Derivation.conjunctionRight facts)
      (Derivation.implicationIntroduction eq) (Derivation.implicationIntroduction next)
  obtain ⟨opened⟩ := hop
  exact ⟨Derivation.existentialElimination opened forward⟩

#print axioms firstHopGround
end LogicLineages.PersistentMarking.NumberedWindowInternalNeutralFirstHopProof
