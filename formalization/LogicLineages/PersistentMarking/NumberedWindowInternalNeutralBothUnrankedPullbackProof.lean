module
public import LogicLineages.PersistentMarking.NumberedWindowInternalPullbackSyntaxProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralBothUnrankedPullbackTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralRankAccessibilityProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDecodeSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeAlignmentSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityDownwardSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.InverseApplicationProof
public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalNeutralBothUnrankedPullbackProof
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
open NumberedWindowInternalNeutralBothUnrankedPullbackTargets
open NumberedWindowInternalNeutralRankTargets (RankDrop)
open NumberedWindowInternalNeutralRankAccessibilityProof (exact_OpenRankAccessibility)
open NumberedWindowInternalFreshProbeProof (optionGraphCases)
open NumberedWindowInternalSparseDecodeSyntaxProof (unaryInputsRename)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary z)
open NumberedWindowInternalFreshProbeAlignmentSyntaxProof (carrierRename)
open ID1Completion.InternalTagArithmeticSyntaxProof (zRelabel)
open ID1Completion.InternalComputabilityDownwardSyntaxProof (edgeRename)

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

private theorem onlyAtZero (s : Data) (g : Program 1) (p : Program 3) (c : Nat)
    (drop : RankDrop s g c) (targets : EdgeTargetCarriers s c)
    (forward : BothUnrankedForwardRule s g p c)
    {α : Type} {Γ : List (Formula α)} (f a x : OTerm α)
    (cx : Nonempty (Derivation (sourceBody s c) Γ (carrier s false c f)))
    (rankZero : Nonempty (Derivation (sourceBody s c) Γ (unary g z f)))
    (app : Nonempty (Derivation (sourceBody s c) Γ (accepts p f a x)))
    (hs : Nonempty (Derivation (sourceBody s c) Γ (descendants s p c a x))) :
    Nonempty (Derivation (sourceBody s c) Γ (membership false f)) := by
  apply membershipIntroduction s c f cx
  intro β ρ Δ f' keep nextEdge
  let source := f.relabel ρ
  let arg := a.relabel ρ
  let out := x.relabel ρ
  have tails := renameInto hs ρ Δ keep
  rw [descendantsRename] at tails
  have call := renameInto app ρ Δ keep
  rw [acceptsRename] at call
  have zero := renameInto rankZero ρ Δ keep
  rw [unaryRename,zRelabel] at zero
  apply optionGraphCases g (![f'] : Fin 1 → OTerm β) (membership false f')
  · intro γ η Ω retains targetZero
    rw [unaryInputsRename] at targetZero
    rw [membershipRename]
    have t := renameInto tails η Ω retains
    rw [descendantsRename] at t
    have movedCall := renameInto call η Ω retains
    rw [acceptsRename] at movedCall
    have q := renameInto zero η Ω retains
    rw [unaryRename,zRelabel] at q
    have e := renameInto nextEdge η Ω retains
    rw [edgeRename] at e
    exact forwardStep s p c (f'.relabel η) (arg.relabel η) (out.relabel η) t
      (forward γ Ω (source.relabel η) (f'.relabel η) (arg.relabel η) (out.relabel η) q targetZero movedCall e)
  · intro γ η Ω k retains targetRank
    rw [unaryInputsRename] at targetRank
    rw [membershipRename]
    have cy := targets β Δ source f' nextEdge
    have carried := renameInto cy η Ω retains
    rw [carrierRename] at carried
    exact exact_OpenRankAccessibility drop k (f'.relabel η) carried targetRank

private theorem inverseStep (i j g : Program 1) (r d p : Program 3) (c : Nat)
    (guards : InputGuards i j r d p) (drop : RankDrop (data i j r d) g c)
    (targets : EdgeTargetCarriers (data i j r d) c)
    (forward : BothUnrankedForwardRule (data i j r d) g p c)
    {α : Type} {Γ : List (Formula α)} (a x : OTerm α)
    (hs : Nonempty (Derivation (sourceBody (data i j r d) c) Γ (descendants (data i j r d) p c a x))) :
    Nonempty (Derivation (sourceBody (data i j r d) c) Γ (inverse p a x)) := by
  let s := data i j r d
  let B := sourceBody s c
  let f : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let A := accepts p f (a.relabel Sum.inl) (x.relabel Sum.inl)
  let Δ := A :: Γ.map weaken
  have app : Nonempty (Derivation B Δ A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have carrierF := (guards c B _ Δ f _ _ app).1
  have hs' := renameInto hs Sum.inl Δ (fun t ht => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨t,ht,rfl⟩))
  rw [descendantsRename] at hs'
  have result : Nonempty (Derivation B Δ (membership false f)) := by
    apply optionGraphCases g (![f] : Fin 1 → OTerm (α ⊕ Fin 1)) (membership false f)
    · intro β ρ Ω keep zero
      rw [unaryInputsRename] at zero
      rw [membershipRename]
      have carried := renameInto carrierF ρ Ω keep
      rw [carrierRename] at carried
      have tails := renameInto hs' ρ Ω keep
      rw [descendantsRename] at tails
      have call := renameInto app ρ Ω keep
      change Nonempty (Derivation B Ω ((accepts p f (a.relabel Sum.inl) (x.relabel Sum.inl)).relabel ρ)) at call
      rw [acceptsRename] at call
      exact onlyAtZero s g p c drop targets forward (f.relabel ρ) ((a.relabel Sum.inl).relabel ρ)
        ((x.relabel Sum.inl).relabel ρ) carried zero call tails
    · intro β ρ Ω k keep rankF
      rw [unaryInputsRename] at rankF
      rw [membershipRename]
      have carried := renameInto carrierF ρ Ω keep
      rw [carrierRename] at carried
      exact exact_OpenRankAccessibility drop k (f.relabel ρ) carried rankF
  obtain ⟨result⟩ := result
  exact ⟨Derivation.universalIntroduction (Derivation.implicationIntroduction result)⟩

/-- Same original inverse slice induction: positively ranked inputs are
handled via real object rank accessibility, as are positively ranked
destinations with actual edge-derived carriers. Only a zero/zero edge
requires an original forward image. -/
theorem exact_InternalBothUnrankedPullback (i j g : Program 1) (r d p : Program 3) (c : Nat)
    (guards : InputGuards i j r d p) (drop : RankDrop (data i j r d) g c)
    (targets : EdgeTargetCarriers (data i j r d) c)
    (forward : BothUnrankedForwardRule (data i j r d) g p c) :
    Pullback (data i j r d) p c := by
  intro α Γ f a x app accessible
  let s := data i j r d
  let θ := invariant p a
  let pre := replacedBody (sliceBody s c false) θ
  have step : Nonempty (Derivation (sourceBody s c) [pre] θ) := by
    have h : Derivation (sourceBody s c) [pre] pre := Derivation.hypothesis List.mem_cons_self
    change Derivation _ [pre] (replacedBody (sliceBody s c false) (invariant p a)) at h
    rw [slice] at h
    exact inverseStep i j g r d p c guards drop targets forward (a.relabel Sum.inl) (.var (.inr 0))
      ⟨Derivation.conjunctionRight h⟩
  have induction := ID1Completion.InternalSliceInductionProof.actualInternalSliceInduction s c α [] false θ x step
  change Nonempty (Derivation _ [] ((membership false x).imp (instantiate (invariant p a) (emb x)))) at induction
  rw [atResult] at induction
  exact inverseElim p a x f (ID1Completion.InternalRecursionClosureLogicProof.closedApply induction accessible) app

#print axioms exact_InternalBothUnrankedPullback
end LogicLineages.PersistentMarking.NumberedWindowInternalNeutralBothUnrankedPullbackProof
