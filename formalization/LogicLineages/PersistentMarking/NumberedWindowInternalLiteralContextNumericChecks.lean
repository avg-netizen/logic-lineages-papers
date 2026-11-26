module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunChecks
public import LogicLineages.PersistentMarking.NumberedWindowRawContextOwnFuelProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralContextNumericChecks
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowRawContextAlgorithm (RawRoot next)
open NumberedWindowFieldAlgorithm (unpackNode packNode)
open NumberedWindowRawContextOwnFuelProof (exact_RawContextOwnHop exact_RawFunctionOwnHop)
open NumberedWindowInternalSparseRawRunChecks (exact_OriginalOwnRawRun)
open NumberedWindowInternalSparseRawTickTargets (ActualRoot ActualFallback)
open NumberedWindowInternalSparseRawRun (ownRun)

/-- On the actual calibrated sparse programs, a genuine non-root
contextual transition gives exact equality of the original own-run
outputs. Arbitrary raw syntax, ordered fields and calibrations are
retained, not reconstructed from typed terms. -/
theorem exact_EvaluatedContextOwnHop (root : RawRoot) (p other : Program 3)
    (cal : ActualRoot root p) (fall : ActualFallback other)
    {a old b tag q w r : Nat} {ws : List Nat}
    (nonroot : tag ≠ 0) (parsed : unpackNode old = some (tag,ws))
    (moves : next tag ws a b = some (q,w,r)) :
    evaluate (ownRun p other) (a ::ᵥ old ::ᵥ b ::ᵥ nil) =
    evaluate (ownRun p other) (q ::ᵥ w ::ᵥ r ::ᵥ nil) := by
  rw [exact_OriginalOwnRawRun root p other cal fall,exact_OriginalOwnRawRun root p other cal fall]
  exact congrArg Bool.toNat (exact_RawContextOwnHop root nonroot parsed moves)

/-- Exact selected function-side tape and exact child's own fuel as an
equality of evaluations, as distinct from an object-graph derivation. -/
theorem exact_EvaluatedFunctionOwnHop (root : RawRoot) (p other : Program 3)
    (cal : ActualRoot root p) (fall : ActualFallback other)
    (dom cod arg q w r : Nat) :
    evaluate (ownRun p other)
      (packNode 6 [dom,cod,q,arg] ::ᵥ packNode 5 [w] ::ᵥ packNode 6 [dom,cod,r,arg] ::ᵥ nil) =
    evaluate (ownRun p other) (q ::ᵥ w ::ᵥ r ::ᵥ nil) := by
  rw [exact_OriginalOwnRawRun root p other cal fall,exact_OriginalOwnRawRun root p other cal fall]
  exact congrArg Bool.toNat (exact_RawFunctionOwnHop root dom cod arg q w r)

#print axioms exact_EvaluatedContextOwnHop
#print axioms exact_EvaluatedFunctionOwnHop
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralContextNumericChecks
