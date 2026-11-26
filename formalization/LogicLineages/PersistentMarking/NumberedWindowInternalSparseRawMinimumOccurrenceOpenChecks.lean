module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawMinimumOccurrenceTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawMinimumOccurrenceOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawMinimumOccurrenceOpenBranchesProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDecodeSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawMinimumOccurrenceOpenChecks
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb)
open NumberedWindowInternalFreshProbeProof (optionGraphCases)
open NumberedWindowInternalSparseDecodeSyntaxProof (unaryInputsRename)
open NumberedWindowInternalSparseFieldParser (parser)
open NumberedWindowInternalSparseRawMinimumOccurrence
open NumberedWindowInternalSparseRawMinimumOccurrenceTargets
open NumberedWindowInternalSparseRawMinimumOccurrenceOpenSyntaxProof
open NumberedWindowInternalSparseRawMinimumOccurrenceOpenBranchesProof (reject present)

attribute [local irreducible] programGraph

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem recover (raw selected : OTerm α)
    (accepted : Nonempty (Derivation body Γ (rawMinimumGraph raw selected))) :
    Nonempty (Derivation body Γ (parsedOccurrence raw selected)) := by
  apply optionGraphCases parser (![raw] : Fin 1 → OTerm α) (parsedOccurrence raw selected)
  · intro β j Δ keep missing
    rw [unaryInputsRename] at missing
    rw [occurrenceRename]
    have h := renameInto accepted j Δ keep
    rw [rawMinimumRename] at h
    exact reject (raw.relabel j) (selected.relabel j) missing h
  · intro β j Δ scratch keep known
    rw [unaryInputsRename] at known
    rw [occurrenceRename]
    have h := renameInto accepted j Δ keep
    rw [rawMinimumRename] at h
    obtain ⟨witness⟩ := present (raw.relabel j) scratch (selected.relabel j) known h
    rw [occurrenceUnfold]
    apply Nonempty.intro
    apply Derivation.existentialIntroduction (emb scratch)
    rw [occurrenceInstance]
    exact witness

theorem exact_OpenRawMinimumParsedOccurrence : ExactOpenRawMinimumParsedOccurrence := by
  intro body α Γ raw selected
  obtain ⟨d⟩ := recover (body := body) (Γ := rawMinimumGraph raw selected :: Γ)
    raw selected ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction d⟩

#print axioms exact_OpenRawMinimumParsedOccurrence
end LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawMinimumOccurrenceOpenChecks
