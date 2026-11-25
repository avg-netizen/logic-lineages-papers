module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCoveredEdgeCoherenceProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalOriginalPairedPackedLeastChecks

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralPairedEdgeCoherenceProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparseCoverGuardedExchangeTargets (guardedExchange)
open NumberedWindowInternalMeasuredPairedGuardedThinNumericProof (pairedExchange)
open NumberedWindowInternalOriginalPairedPackedLeastChecks (exact_OpenOriginalPairedPackedLeast)
open NumberedWindowInternalLiteralCoveredMemo (coveredMemoWindow)
open NumberedWindowInternalLiteralCoveredEdgeCoherenceProof
  (SelectedMinimumEquality exact_OpenCoveredCoherenceFromMinimumEquality)
open NumberedWindowInternalLiteralRoundLeastTargets (SameLeastOnEdge)

/-- Compare the actual packed least results, for an arbitrary physical
window and the actual guarded pairing. No extensional substitution for
either program is made. -/
theorem exact_OriginalPairedSelectedMinimum (C : Program 3) (d : Program 2)
    (W : Program 3) (s : Settings) :
    SelectedMinimumEquality C (guardedExchange C s (pairedExchange d)) W s := by
  intro B α Γ ctx ty a b x y edge left right
  exact exact_OpenOriginalPairedPackedLeast C d W s ctx ty a b x y left right edge

/-- The literal memo supplies the physical domains for both endpoints;
the original paired least theorem now pays the equality premise. -/
theorem exact_OriginalPairedCoveredCoherence (C : Program 3) (d : Program 2)
    (s : Settings) (base : Program 2) (T V : Program 1) :
    SameLeastOnEdge C (guardedExchange C s (pairedExchange d)) (coveredMemoWindow C s base T V) s :=
  exact_OpenCoveredCoherenceFromMinimumEquality C (guardedExchange C s (pairedExchange d))
    s base T V (exact_OriginalPairedSelectedMinimum C d (coveredMemoWindow C s base T V) s)

#print axioms exact_OriginalPairedSelectedMinimum
#print axioms exact_OriginalPairedCoveredCoherence
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralPairedEdgeCoherenceProof
