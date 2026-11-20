module
public import LogicLineages.PersistentMarking.NumberedWindowInternalPullbackSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.InverseApplicationProof
public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalPullbackChecks
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalAccessibilityRules
open ID1Completion.SourcePresentation SourceComputabilityFormulaSupportProof ID1Completion.InternalSliceInduction
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open ID1Completion.InternalTagArithmeticSyntaxProof (OTerm emb)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.SourceComputabilityCompletion.InverseApplicationSyntaxProof (membershipRename)
open ID1Completion.SourceComputabilityCompletion.InverseApplicationProof (membershipIntroduction)
open NumberedWindowInternalPullbackTargets NumberedWindowInternalPullbackSyntaxProof
open NumberedWindowInternalPresentationTargets (data)
open NumberedWindowGuardedGraphTargets (InputGuards)
open NumberedWindowComputabilityFormulaTargets (accepts)

private theorem forwardStep (s : Data) (p : Program 3) (c : Nat) {α : Type} {Γ : List (Formula α)}
    (g a x : OTerm α)
    (hs : Nonempty (Derivation (sourceBody s c) Γ (descendants s p c a x)))
    (hforward : Nonempty (Derivation (sourceBody s c) Γ (forwardImage s p c g a x))) :
    Nonempty (Derivation (sourceBody s c) Γ (membership false g)) := by
  let y : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let E := accepts p (g.relabel Sum.inl) (a.relabel Sum.inl) y ⊓ edge s false c (x.relabel Sum.inl) y
  let Δ := E :: Γ.map weaken
  have hs' := renameInto hs Sum.inl Δ (fun t ht => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨t,ht,rfl⟩))
  rw [descendantsRename] at hs'
  have pair : Derivation (sourceBody s c) Δ E := Derivation.hypothesis List.mem_cons_self
  have hy := descend s p c (a.relabel Sum.inl) (x.relabel Sum.inl) y hs' ⟨Derivation.conjunctionRight pair⟩
  obtain ⟨hg⟩ := inverseElim p (a.relabel Sum.inl) y (g.relabel Sum.inl) hy ⟨Derivation.conjunctionLeft pair⟩
  obtain ⟨hforward⟩ := hforward
  apply Nonempty.intro
  apply Derivation.existentialElimination hforward
  change Derivation _ Δ ((membership false g).relabel Sum.inl)
  rw [membershipRename]
  exact hg

private theorem inverseStep (i j : Program 1) (r d p : Program 3) (c : Nat)
    (guards : InputGuards i j r d p) (forward : ForwardRule (data i j r d) p c)
    {α : Type} {Γ : List (Formula α)} (a x : OTerm α)
    (hs : Nonempty (Derivation (sourceBody (data i j r d) c) Γ (descendants (data i j r d) p c a x))) :
    Nonempty (Derivation (sourceBody (data i j r d) c) Γ (inverse p a x)) := by
  let s := data i j r d
  let f : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let A := accepts p f (a.relabel Sum.inl) (x.relabel Sum.inl)
  let Δ := A :: Γ.map weaken
  have app : Nonempty (Derivation (sourceBody s c) Δ A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have carrierF := (guards c (sourceBody s c) _ Δ f _ _ app).1
  have hs' := renameInto hs Sum.inl Δ (fun t ht => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨t,ht,rfl⟩))
  rw [descendantsRename] at hs'
  have result : Nonempty (Derivation (sourceBody s c) Δ (membership false f)) := by
    apply membershipIntroduction s c f carrierF
    intro β k Ω g hk hedge
    have hs'' := renameInto hs' k Ω hk
    rw [descendantsRename] at hs''
    have app' := renameInto app k Ω hk
    change Nonempty (Derivation _ Ω ((accepts p f (a.relabel Sum.inl) (x.relabel Sum.inl)).relabel k)) at app'
    rw [acceptsRename] at app'
    exact forwardStep s p c g _ _ hs'' (forward _ Ω _ g _ _ app' hedge)
  obtain ⟨result⟩ := result
  exact ⟨Derivation.universalIntroduction (Derivation.implicationIntroduction result)⟩

theorem exact_InternalPullback : InternalPullback := by
  intro i j r d p c guards forward α Γ f a x app accessible
  let s := data i j r d
  let θ := invariant p a
  let pre := replacedBody (sliceBody s c false) θ
  have step : Nonempty (Derivation (sourceBody s c) [pre] θ) := by
    have h : Derivation (sourceBody s c) [pre] pre := Derivation.hypothesis List.mem_cons_self
    change Derivation _ [pre] (replacedBody (sliceBody s c false) (invariant p a)) at h
    rw [slice] at h
    exact inverseStep i j r d p c guards forward (a.relabel Sum.inl) (.var (.inr 0))
      ⟨Derivation.conjunctionRight h⟩
  have induction := ID1Completion.InternalSliceInductionProof.actualInternalSliceInduction s c α [] false θ x step
  change Nonempty (Derivation _ [] ((membership false x).imp (instantiate (invariant p a) (emb x)))) at induction
  rw [atResult] at induction
  exact inverseElim p a x f (ID1Completion.InternalRecursionClosureLogicProof.closedApply induction accessible) app

#print axioms exact_InternalPullback
end LogicLineages.PersistentMarking.NumberedWindowInternalPullbackChecks
