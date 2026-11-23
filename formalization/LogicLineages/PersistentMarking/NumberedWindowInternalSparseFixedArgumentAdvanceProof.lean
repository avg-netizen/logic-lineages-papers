module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFixedArgumentClassHopProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAcceptedHopCasesProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathSuccessfulAdvanceGraphSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphStepSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseFixedArgumentAdvanceProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc rawCons)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (rawConsRename)
open NumberedWindowInternalSparsePathSuccessfulAdvanceGraphSyntaxProof (graph5Rename)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm functionWitnessTerm)
open NumberedWindowInternalCoverCombinedRestrictedFormationTargets (thinFormation)
open NumberedWindowInternalCoverCombinedRestrictedWrapperTargets (thinMatchingWindow)
open NumberedWindowInternalSparseFixedArgumentRawHopProof (formationRename)
open NumberedWindowInternalSparseFixedArgumentClassHopProof (classHopCases)
open NumberedWindowInternalSparseAcceptedHopCasesProof (advanceCases)
open NumberedWindowInternalSparsePathAdvanceTargets (selectedGraph actualCalls)
open NumberedWindowInternalSparseTypedRaw (typedRaw5)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)
open NumberedWindowInternalSparsePackedLeast (packedLeastProgram)
open NumberedWindowInternalSparseAddressSingletonTargets (singletonCertificate)
open NumberedWindowInternalSparsePositiveHeadDecompositionTargets (positiveAt)

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem callsRename {β : Type} (raw : Program 5) (least : Program 3)
    (ctx ty src dst q w r : OTerm α) (j : α → β) :
    (actualCalls raw least ctx ty src dst q w r).relabel j =
      actualCalls raw least (ctx.relabel j) (ty.relabel j) (src.relabel j) (dst.relabel j)
        (q.relabel j) (w.relabel j) (r.relabel j) := by
  simp only [actualCalls,conjunctionRename]
  rw [graph5Rename]
  simp only [programRename,tripleInputsRename,sucRelabel,zRelabel]

/-- An actual original successful advance creates a genuine lifted typed
singleton on the same fixed raw argument. The callback retains the original
raw step/least relations; importantly q and r were not replaced by their
function class representatives. -/
theorem mapAdvanceCases (C root other baseW : Program 3) (X : Program 2) (s : Settings) (V : Program 1)
    (ctx dom cod arg src hop dst : OTerm α) (goal : Formula α) :
    let W := thinMatchingWindow C s baseW V
    let raw := typedRaw5 root other W V
    let least := packedLeastProgram C X W s
    Nonempty (Derivation body Γ (thinFormation W ctx dom cod arg)) →
    Nonempty (Derivation body Γ (selectedGraph raw least (suc dst) ctx (rawCons dom cod) (suc src) hop)) →
    (∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (q w r a b : OTerm β),
      let l := auxiliaryTerm (dom.relabel j) (cod.relabel j) q (arg.relabel j)
      let y := auxiliaryTerm (dom.relabel j) (cod.relabel j) r (arg.relabel j)
      (∀ p ∈ Γ, p.relabel j ∈ Δ) →
      Nonempty (Derivation body Δ (actualCalls raw least (ctx.relabel j)
        (rawCons (dom.relabel j) (cod.relabel j)) (src.relabel j) (dst.relabel j) q w r)) →
      Nonempty (Derivation body Δ (leastGraph C X W s (ctx.relabel j) (cod.relabel j) l a)) →
      Nonempty (Derivation body Δ (leastGraph C X W s (ctx.relabel j) (cod.relabel j) y b)) →
      Nonempty (Derivation body Δ (positiveAt raw least (ctx.relabel j) (cod.relabel j) a
        (singletonCertificate b l (functionWitnessTerm w) y) b)) →
      Nonempty (Derivation body Δ (goal.relabel j))) →
    Nonempty (Derivation body Γ goal) := by
  intro W raw least ready advance next
  apply advanceCases raw least ctx (rawCons dom cod) src hop dst goal advance
  intro β j Δ q w r keep _ original
  have hf := renameInto ready j Δ keep
  rw [formationRename] at hf
  rw [rawConsRename] at original
  obtain ⟨d⟩ := original
  have step : Nonempty (Derivation body Δ (programGraph raw (suc z)
      ![ctx.relabel j,rawCons (dom.relabel j) (cod.relabel j),q,w,r])) :=
    ⟨Derivation.conjunctionLeft d⟩
  apply classHopCases C root other baseW X s V (ctx.relabel j) (dom.relabel j) (cod.relabel j)
    (arg.relabel j) q w r (goal.relabel j) hf step
  intro γ k Θ a b leftAux rightAux preserve lcall rcall mapped
  have parent := renameInto (Nonempty.intro d) k Θ preserve
  rw [callsRename,rawConsRename] at parent
  have all : ∀ p ∈ Γ, p.relabel (k ∘ j) ∈ Θ := by
    intro p hp
    simpa only [formulaRelabelComposition] using preserve (p.relabel j) (keep p hp)
  have final := next γ (k ∘ j) Θ (q.relabel k) (w.relabel k) (r.relabel k) a b all
    (by simpa only [Term.relabel_relabel] using parent)
    (by simpa only [leftAux,W,Term.relabel_relabel] using lcall)
    (by simpa only [rightAux,W,Term.relabel_relabel] using rcall)
    (by simpa only [leftAux,rightAux,W,raw,least,Term.relabel_relabel] using mapped)
  simpa only [formulaRelabelComposition] using final

#print axioms mapAdvanceCases
end LogicLineages.PersistentMarking.NumberedWindowInternalSparseFixedArgumentAdvanceProof
