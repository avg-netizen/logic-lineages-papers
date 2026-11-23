module
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectCoreTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSharedTapeTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalDirectCoreSharedTapeTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalDirectCoreTargets (dCore)
open NumberedWindowInternalDirectSharedTapeTargets (Reports)
open NumberedWindowInternalDirectBoundaryGuardsTargets (boundaryRaw)
open NumberedWindowInternalDirectWitnessEnvelopeTargets (reports tripleTerm)
open NumberedWindowInternalDirectSourcePartitionRawTargets (sourceTape)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)

/-- A single actual tag-5 accepted envelope supplies the original certificate
and raw endpoints, the physical typed/nonempty boundary, and one common scratch
tape. One identical observer is used on the two exact ordered partitions. -/
def ExactOpenDCoreSharedTape : Prop :=
  ∀ (scalar : Program 1) (positive : Program 3) (count : Program 2)
    (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (src w dst : OTerm α) (goal : Formula α),
    Nonempty (Derivation B Γ (programGraph (dCore scalar positive count) (suc z) (sourceTape src w dst))) →
    (∀ (β : Type) (j : α → β) (Δ : List (Formula β))
        (kept removed inserted s t k d a p sk tp : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      Nonempty (Derivation B Δ (reports 5 (w.relabel j) kept removed inserted)) →
      Nonempty (Derivation B Δ (equal (w.relabel j) (tripleTerm 5 kept removed inserted))) →
      Nonempty (Derivation B Δ (programGraph (boundaryRaw scalar) (suc z)
        (sourceTape (src.relabel j) (dst.relabel j) removed))) →
      Reports count count positive B Δ (src.relabel j) (dst.relabel j)
        kept removed inserted s t k d a p sk tp →
      Nonempty (Derivation B Δ (goal.relabel j))) →
    Nonempty (Derivation B Γ goal)

end LogicLineages.PersistentMarking.NumberedWindowInternalDirectCoreSharedTapeTargets
