module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCoveredEdgeCoherenceProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScalarEdgeOpenChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralFormingCoherenceProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalControlGraphSupportProof (outputTransport programRename)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn sucRelabel zRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (congSuc symm)
open ID1Completion.InternalBetaTotalityProof (addHyp)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalLiteralCoveredEdgeCoherenceProof (SelectedMinimumEquality)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalLiteralRoundLeastTargets (SameLeastOnEdge)
open NumberedWindowInternalLiteralRootDispatchOpenProof (D)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc)
open NumberedWindowInternalSparseScalarEdge (edge4)
open NumberedWindowInternalSparseDirectedSeen (acceptEdge edgeTape)
open NumberedWindowInternalSparsePackedLeast (packedLeastProgram)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)
open NumberedWindowInternalSparsePackedLeastOpenSyntaxProof (leastRename)
open NumberedWindowInternalSparsePackedDomainTargets (hasLeast)
open NumberedWindowInternalSparsePackedDomainSyntaxProof (casesLeast)
open NumberedWindowInternalSparseScalarEdgeOpenChecks (exact_OpenPackedScalarEdge)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (quadInputsRename)

attribute [local irreducible] programGraph

private theorem acceptedEdgeRename {α β : Type} (E : Program 4) (ctx ty w k : OTerm α) (j : α → β) :
    (acceptEdge E ctx ty w k).relabel j = acceptEdge E (ctx.relabel j) (ty.relabel j)
      (w.relabel j) (k.relabel j) := by
  simp only [acceptEdge,programRename,edgeTape,quadInputsRename,sucRelabel,zRelabel]

private theorem moveValue {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings)
    (ctx ty a x y : OTerm α) (e : D B Γ (eqn x y)) (held : D B Γ (leastGraph C X W s ctx ty a x)) :
    D B Γ (leastGraph C X W s ctx ty a y) := by
  obtain ⟨proof⟩ := e
  exact outputTransport (packedLeastProgram C X W s) (suc x) (suc y)
    ![ctx,ty,a] ⟨congSuc proof⟩ held

/-- The edge itself supplies the two window queries. Any selected window
that makes their least domains available admits the same bidirectional
coherence from the actual selected-minimum equality theorem. -/
theorem exact_OpenCoherenceFromWindowDomain (C : Program 3) (X : Program 2) (W : Program 3)
    (s : Settings) (paid : SelectedMinimumEquality C X W s)
    (domain : ∀ (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (ctx ty a : OTerm α),
      D B Γ (windowAt W ctx ty a) → D B Γ (hasLeast C X W s ctx ty a)) :
    SameLeastOnEdge C X W s := by
  intro B α Γ ctx ty a b x
  let E := acceptEdge (edge4 X W) ctx ty a b
  let P := leastGraph C X W s ctx ty a x
  let Q := leastGraph C X W s ctx ty b x
  let Δ := E :: Γ
  have arc : Derivation B Δ E := Derivation.hypothesis List.mem_cons_self
  obtain ⟨dec⟩ := exact_OpenPackedScalarEdge X W B α Δ ctx ty a b
  let guards := Derivation.conjunctionRight (Derivation.implicationElimination (Derivation.conjunctionLeft dec) arc)
  obtain ⟨domainL⟩ := domain B α Δ ctx ty a ⟨Derivation.conjunctionLeft guards⟩
  obtain ⟨domainR⟩ := domain B α Δ ctx ty b ⟨Derivation.conjunctionRight guards⟩
  have lr : D B (P :: Δ) Q := by
    apply casesLeast C X W s ctx ty b Q (⟨addHyp domainR P⟩)
    intro β j Θ y keep atY
    rw [leastRename]
    have e := renameInto (⟨addHyp arc P⟩ : D B (P :: Δ) E) j Θ keep
    change D B Θ ((acceptEdge (edge4 X W) ctx ty a b).relabel j) at e
    rw [acceptedEdgeRename] at e
    have l := renameInto (⟨Derivation.hypothesis List.mem_cons_self⟩ : D B (P :: Δ) P) j Θ keep
    change D B Θ ((leastGraph C X W s ctx ty a x).relabel j) at l
    rw [leastRename] at l
    obtain ⟨same⟩ := paid B β Θ (ctx.relabel j) (ty.relabel j) (a.relabel j) (b.relabel j) (x.relabel j) y e l atY
    exact moveValue C X W s _ _ _ _ _ ⟨symm same⟩ atY
  have rl : D B (Q :: Δ) P := by
    apply casesLeast C X W s ctx ty a P (⟨addHyp domainL Q⟩)
    intro β j Θ y keep atY
    rw [leastRename]
    have e := renameInto (⟨addHyp arc Q⟩ : D B (Q :: Δ) E) j Θ keep
    change D B Θ ((acceptEdge (edge4 X W) ctx ty a b).relabel j) at e
    rw [acceptedEdgeRename] at e
    have r := renameInto (⟨Derivation.hypothesis List.mem_cons_self⟩ : D B (Q :: Δ) Q) j Θ keep
    change D B Θ ((leastGraph C X W s ctx ty b x).relabel j) at r
    rw [leastRename] at r
    have same := paid B β Θ (ctx.relabel j) (ty.relabel j) (a.relabel j) (b.relabel j) y (x.relabel j) e atY r
    exact moveValue C X W s _ _ _ _ _ same atY
  obtain ⟨forward⟩ := lr
  obtain ⟨back⟩ := rl
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
    (Derivation.conjunctionIntroduction domainL domainR)
    (Derivation.conjunctionIntroduction (Derivation.implicationIntroduction forward) (Derivation.implicationIntroduction back)))⟩

#print axioms exact_OpenCoherenceFromWindowDomain
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralFormingCoherenceProof
