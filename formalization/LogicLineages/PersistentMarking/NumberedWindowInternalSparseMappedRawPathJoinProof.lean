module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseMappedRawPathReportProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFixedArgumentAdjacentProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveHeadDecompositionFinishSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseMappedRawPathJoinProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePackedLeast (packedLeastProgram)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparsePositiveHeadDecompositionTargets (positiveAt)
open NumberedWindowInternalSparsePositiveTransitivityTargets (supplied)
open NumberedWindowInternalSparsePositiveHeadDecompositionFinishSyntaxProof (positiveRename)
open NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof (auxiliaryRename)
open NumberedWindowInternalSparseFixedArgumentAdjacentProof (composeAdjacent)
open NumberedWindowInternalSparseMappedRawPathReportProof

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem package {raw : Program 5} {least : Program 3}
    (ctx ty l r a b : OTerm α)
    (ll : Nonempty (Derivation body Γ (leastAt least ctx ty l a)))
    (rl : Nonempty (Derivation body Γ (leastAt least ctx ty r b)))
    (accepted : Nonempty (Derivation body Γ (supplied raw least ctx ty a b))) :
    Nonempty (Derivation body Γ (mapped raw least ctx ty l r)) := by
  obtain ⟨someCert⟩ := accepted
  let j : α → α ⊕ Fin 1 := Sum.inl
  let w : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let E := positiveAt raw least (ctx.relabel j) (ty.relabel j) (a.relabel j) w (b.relabel j)
  let Δ := E :: Γ.map weaken
  have keep : ∀ p ∈ Γ, p.relabel j ∈ Δ :=
    fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
  have left := renameInto ll j Δ keep
  have right := renameInto rl j Δ keep
  rw [leastRename] at left right
  obtain ⟨lG⟩ := left
  obtain ⟨rG⟩ := right
  have cG : Derivation body Δ E := Derivation.hypothesis List.mem_cons_self
  have composed := provide raw least (ctx.relabel j) (ty.relabel j) (l.relabel j) (r.relabel j)
    (a.relabel j) (b.relabel j) w
    ⟨Derivation.conjunctionIntroduction lG (Derivation.conjunctionIntroduction rG cG)⟩
  obtain ⟨d⟩ := composed
  apply Nonempty.intro
  apply Derivation.existentialElimination someCert
  change Derivation body Δ ((mapped raw least ctx ty l r).relabel j)
  rw [mappedRename]
  exact d

/-- Attach an actual positive prefix to the object-reported mapped suffix.
The joining raw function mid is the same term on both sides. -/
theorem prepend (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings)
    (raw : Program 5) (ctx dom cod arg l mid r a b cert : OTerm α) :
    let least := packedLeastProgram C X W s
    let m := auxiliaryTerm dom cod mid arg
    Nonempty (Derivation body Γ (leastAt least ctx cod l a)) →
    Nonempty (Derivation body Γ (leastAt least ctx cod m b)) →
    Nonempty (Derivation body Γ (positiveAt raw least ctx cod a cert b)) →
    Nonempty (Derivation body Γ (mapped raw least ctx cod m r)) →
    Nonempty (Derivation body Γ (mapped raw least ctx cod l r)) := by
  intro least m ll ml h tail
  apply casesMapped raw least ctx cod m r _ tail
  intro β j Δ a₂ b₂ cert₂ keep suffix
  rw [mappedRename]
  have lh := renameInto ll j Δ keep
  have mh := renameInto ml j Δ keep
  rw [leastRename] at lh mh
  have ph := renameInto h j Δ keep
  rw [positiveRename] at ph
  have mh' : Nonempty (Derivation body Δ
      (leastAt least (ctx.relabel j) (cod.relabel j)
        (auxiliaryTerm (dom.relabel j) (cod.relabel j) (mid.relabel j) (arg.relabel j)) (b.relabel j))) := by
    simpa only [m,auxiliaryRename] using mh
  obtain ⟨rows⟩ := suffix
  have second := Derivation.conjunctionRight rows
  have secondStart : Nonempty (Derivation body Δ
      (leastAt least (ctx.relabel j) (cod.relabel j)
        (auxiliaryTerm (dom.relabel j) (cod.relabel j) (mid.relabel j) (arg.relabel j)) a₂)) := by
    simpa only [m,auxiliaryRename] using
      (Nonempty.intro (Derivation.conjunctionLeft rows))
  have splice := composeAdjacent C X W s raw
    (ctx.relabel j) (dom.relabel j) (cod.relabel j) (arg.relabel j) (mid.relabel j)
    (a.relabel j) (cert.relabel j) (b.relabel j) a₂ cert₂ b₂ mh' secondStart ph
    ⟨Derivation.conjunctionRight second⟩
  exact package (ctx.relabel j) (cod.relabel j) (l.relabel j) (r.relabel j)
    (a.relabel j) b₂ lh ⟨Derivation.conjunctionLeft second⟩ splice

#print axioms prepend
end LogicLineages.PersistentMarking.NumberedWindowInternalSparseMappedRawPathJoinProof
