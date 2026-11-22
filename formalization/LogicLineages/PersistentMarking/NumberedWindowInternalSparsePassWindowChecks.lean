module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedSeenOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScalarEdgeOpenChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowChecks
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalBetaTotalityProof (addHyp disjunctionElimination)
open ID1Completion.InternalControlGraphSupportProof (valueUnique)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalLessThanSupportProof (zeroConstantValue)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn z suc)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseDirectedSeen (acceptEdge edgeTape seenWitness witnessRow)
open NumberedWindowInternalSparseDirectedSeenOpenSyntaxProof (witnessUnfold witnessBinder)
open NumberedWindowInternalSparseDirectedFilter (passGraph)
open NumberedWindowInternalSparseScalarEdge (edge4)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparsePassWindowTargets
open NumberedWindowInternalSparsePassWindowSyntaxProof

theorem exact_RoundEdgeWindows : ExactRoundEdgeWindows := by
  intro X W
  constructor
  · intro body α Γ ctx ty w k
    let A := acceptEdge (constantZero 4) ctx ty w k
    obtain ⟨e⟩ := valueUnique (body := body) (Gamma := A :: Γ) (constantZero 4) (suc z) z
      (edgeTape ctx ty w k) ⟨Derivation.hypothesis List.mem_cons_self⟩ (zeroConstantValue _)
    exact ⟨Derivation.implicationIntroduction (Derivation.explosion (sucNeZeroApply e))⟩
  · intro body α Γ ctx ty w k
    let A := acceptEdge (edge4 X W) ctx ty w k
    obtain ⟨law⟩ := NumberedWindowInternalSparseScalarEdgeOpenChecks.exact_OpenPackedScalarEdge
      X W body α (A :: Γ) ctx ty w k
    have calls := Derivation.implicationElimination (Derivation.conjunctionLeft law)
      (Derivation.hypothesis List.mem_cons_self)
    exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionRight (Derivation.conjunctionRight calls))⟩

private theorem atWitness {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (E : Program 4) (W : Program 3) (paid : TargetWindow E W) (ctx ty seen w k : OTerm α)
    (previous : Nonempty (Derivation body Γ (allWindow W ctx ty seen)))
    (d : Nonempty (Derivation body Γ (witnessRow E seen ctx ty w k))) :
    Nonempty (Derivation body Γ (windowAt W ctx ty k)) := by
  obtain ⟨previous⟩ := previous
  obtain ⟨row⟩ := d
  obtain ⟨guard⟩ := specialize W ctx ty seen w previous
  have atW := Derivation.implicationElimination guard (Derivation.conjunctionLeft row)
  let eq := eqn w k
  obtain ⟨same⟩ := moveGuard (body := body) (Γ := eq :: Γ) W ctx ty w k
    (Derivation.hypothesis List.mem_cons_self) (addHyp atW eq)
  obtain ⟨edge⟩ := paid body α Γ ctx ty w k
  exact ⟨disjunctionElimination (Derivation.conjunctionRight row) (Derivation.implicationIntroduction same) edge⟩

theorem exact_SeenWitnessPreservesWindow : ExactSeenWitnessPreservesWindow := by
  intro E W paid body α Γ ctx ty seen k
  let A := allWindow W ctx ty seen ⊓ seenWitness E seen ctx ty k
  let Δ := A :: Γ
  have input : Derivation body Δ A := Derivation.hypothesis List.mem_cons_self
  have witness := Derivation.conjunctionRight input
  rw [witnessUnfold] at witness
  let j : α → α ⊕ Fin 1 := Sum.inl
  let w : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let Θ := witnessBinder E seen ctx ty k :: Δ.map weaken
  have guarded := renameInto ⟨Derivation.conjunctionLeft input⟩ j Θ
    (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
  rw [allRename] at guarded
  obtain ⟨r⟩ := atWitness (body := body) (Γ := Θ) E W paid
    (ctx.relabel j) (ty.relabel j) (seen.relabel j) w (k.relabel j) guarded
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have final : Derivation body Θ (weaken (windowAt W ctx ty k)) := by
    change Derivation body Θ ((windowAt W ctx ty k).relabel j)
    rwa [windowRename]
  exact ⟨Derivation.implicationIntroduction (Derivation.existentialElimination witness final)⟩

theorem exact_PassWindowFromRetained : ExactPassWindowFromRetained := by
  intro retained E W paid body α Γ ctx ty vertices seen out
  let A := allWindow W ctx ty seen ⊓ passGraph E out vertices seen ctx ty
  let Δ := A :: Γ
  let j : α → α ⊕ Fin 1 := Sum.inl
  let k : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let B := memberGraph (out.relabel j) k
  let Θ := B :: Δ.map weaken
  have input : Derivation body Δ A := Derivation.hypothesis List.mem_cons_self
  have keep (p : Formula α) (hp : p ∈ Δ) : p.relabel j ∈ Θ :=
    List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
  have guard := renameInto ⟨Derivation.conjunctionLeft input⟩ j Θ keep
  have run := renameInto ⟨Derivation.conjunctionRight input⟩ j Θ keep
  rw [allRename] at guard
  rw [passRename] at run
  obtain ⟨guard⟩ := guard
  obtain ⟨run⟩ := run
  obtain ⟨earlier⟩ := retained E body (α ⊕ Fin 1) Θ (vertices.relabel j) (seen.relabel j)
    (ctx.relabel j) (ty.relabel j) (out.relabel j) k
  have successor := Derivation.implicationElimination earlier (Derivation.conjunctionIntroduction run
    (Derivation.hypothesis List.mem_cons_self))
  obtain ⟨step⟩ := exact_SeenWitnessPreservesWindow E W paid body (α ⊕ Fin 1) Θ
    (ctx.relabel j) (ty.relabel j) (seen.relabel j) k
  have live := Derivation.implicationElimination step (Derivation.conjunctionIntroduction guard successor)
  exact ⟨Derivation.implicationIntroduction (Derivation.universalIntroduction (Derivation.implicationIntroduction live))⟩

#print axioms exact_RoundEdgeWindows
#print axioms exact_SeenWitnessPreservesWindow
#print axioms exact_PassWindowFromRetained
end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowChecks
