module
public import LogicLineages.PersistentMarking.NumberedWindowInternalOriginFilterConsCasesTargets
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalOriginFilterConsCasesProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalRawListRecursionProof (consForward stepCases)
open NumberedWindowInternalOriginRowsFilterTargets (zeroBase rowStep)
open NumberedWindowInternalOriginFilterConsCasesTargets

private theorem singletonRename {α β : Type} (p : OrdinaryArithmetic.Term α) (j : α → β) :
    (fun i : Fin 1 => ((![p] : Fin 1 → OrdinaryArithmetic.Term α) i).relabel j) = ![p.relabel j] := by
  funext i
  obtain rfl := Fin.eq_zero i
  rfl

/-- Exposes only the real prior result of the same filter at the actual
tail. The callback uses that same value and the unchanged pool. -/
theorem exact_OpenOriginFilterConsCases : ExactOpenOriginFilterConsCases := by
  intro side B α Γ code head tail pool out goal cell filtered k
  have raw := consForward zeroBase (rowStep side) code head tail out ![pool] cell filtered
  apply stepCases zeroBase (rowStep side) out head tail ![pool] goal raw
  intro β j Δ old kept oldRun stepRun
  rw [singletonRename] at oldRun stepRun
  exact k β j Δ old kept oldRun stepRun

#print axioms exact_OpenOriginFilterConsCases

end LogicLineages.PersistentMarking.NumberedWindowInternalOriginFilterConsCasesProof
