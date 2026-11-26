module
public import LogicLineages.CartierObserverCurrent.ActualRootBoundsTargets
public import LogicLineages.OrdinalComparison.RealResidueBoundsProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.CartierObserverCurrent.ActualRootBounds
open LogicLineages.OrdinalComparison

theorem completeActualBounds : Targets.CompleteActualBounds := by
  intro v hv
  have hu : 4 ≤ Phi v := by have := self_lt_Phi v; omega
  obtain ⟨hr, hd, hpos, hupper, htot, hexp⟩ := fullActualLinkedResidueBounds (Phi v) hu
  have hintpos : (0 : Int) < (actualLinkedDegree (Phi v) : Int) -
      2 * (actualLinkedOffset (Phi v) : Int) := by omega
  have hintupper : (actualLinkedDegree (Phi v) : Int) -
      2 * (actualLinkedOffset (Phi v) : Int) < (actualLinkedModulus (Phi v) : Int) := by omega
  exact ⟨hr, hd, hintpos, hintupper, htot, hexp⟩

#audit_namespace LogicLineages.CartierObserverCurrent.ActualRootBounds
end LogicLineages.CartierObserverCurrent.ActualRootBounds
