module
public import LogicLineages.PersistentMarking.NumberedWindowInternalZeroRankOpenPathBuildProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveIterationBindingProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldExistentialProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalZeroRankPrefixRenameProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalTagArithmeticSyntaxProof (zRelabel sucRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePositiveIterationBindingProof (scratchRename)
open NumberedWindowInternalSparseFieldExistentialProof (consGraphRename)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (quadInputsRename)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalZeroRankOpenPathBuildProof (OriginalZeroPrefix)
attribute [local irreducible] programGraph

/-- Recontextualize each actually held physical row without changing
the selected original program, or replacing its zero-rank report. -/
theorem exact_OriginalZeroPrefixRename {B : Positive (Fin 1)} {α β : Type}
    {Γ : List (Formula α)} {Δ : List (Formula β)} (j : α → β)
    (keep : ∀ f ∈ Γ, f.relabel j ∈ Δ)
    (g : Program 1) (raw : Program 5) (L : Program 3)
    (c ty start cert fuel state cursor current : OTerm α)
    (held : OriginalZeroPrefix B Γ g raw L c ty start cert fuel state cursor current) :
    OriginalZeroPrefix B Δ g raw L (c.relabel j) (ty.relabel j) (start.relabel j) (cert.relabel j)
      (fuel.relabel j) (state.relabel j) (cursor.relabel j) (current.relabel j) := by
  induction held with
  | init h =>
    rw [zRelabel]
    have moved := renameInto h j Δ keep
    rw [scratchRename] at moved
    exact OriginalZeroPrefix.init moved
  | cons priorRows cell step rank after ih =>
    rw [sucRelabel,sucRelabel]
    have c' := renameInto cell j Δ keep
    have s' := renameInto step j Δ keep
    have r' := renameInto rank j Δ keep
    have a' := renameInto after j Δ keep
    rw [consGraphRename] at c'
    simp only [programRename,quadInputsRename,sucRelabel] at s'
    rw [unaryRename,zRelabel] at r'
    rw [scratchRename,sucRelabel] at a'
    exact OriginalZeroPrefix.cons ih c' s' r' a'

#print axioms exact_OriginalZeroPrefixRename
end LogicLineages.PersistentMarking.NumberedWindowInternalZeroRankPrefixRenameProof
