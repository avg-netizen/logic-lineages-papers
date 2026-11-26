module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveIterationCoordinateThinGraphProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveFold

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveIterationCoordinateThinLeavesProof
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalAcceptance (branch constantZero)
open InternalListCodec (headCode tailCode)
open NumberedWindowInternalSparsePositiveIterationCoordinateThinGraphProof
open NumberedWindowInternalSparsePositiveFold

theorem prior : Stable (.projection (1 : Fin 6)) := stableProjection 1 (Or.inl rfl)
theorem context : Stable (.projection (2 : Fin 6)) := stableProjection 2 (Or.inr (Or.inl rfl))
theorem ty : Stable (.projection (3 : Fin 6)) := stableProjection 3 (Or.inr (Or.inr rfl))

theorem unary (p : Program 1) (q : Program 6) (h : Stable q) :
    Stable (.composition p (fun _ : Fin 1 => q)) :=
  stableCompose p (fun _ => q) (fun _ => h)

theorem binary (p : Program 2) (q r : Program 6) (hq : Stable q) (hr : Stable r) :
    Stable (.composition p ![q,r]) :=
  stableCompose p ![q,r] (fun i => Fin.cases hq (Fin.cases hr (fun u => Fin.elim0 u)) i)

theorem choice (c p q : Program 6) (hc : Stable c) (hp : Stable p) (hq : Stable q) :
    Stable (branch c p q) :=
  stableCompose _ _ (fun i => Fin.cases hc
    (Fin.cases hp (Fin.cases hq (fun u => Fin.elim0 u))) i)

theorem cursor : Stable scratchCursor := unary headCode (.projection 1) prior
theorem current : Stable scratchCurrent := unary tailCode (.projection 1) prior
theorem readCell (p : Program 1) : Stable (onCursor p) := unary p scratchCursor cursor

theorem zero : Stable (constantZero 6) :=
  stableCompose .zero Fin.elim0 (fun i => Fin.elim0 i)

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveIterationCoordinateThinLeavesProof
