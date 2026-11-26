module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralEnrichedEdgeProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralPackedLeastOnProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScalarEdgeNumericProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralEdgeObserverFitProof
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open NumberedWindowScalarAlgorithm (Settings edge)
open NumberedWindowFieldAlgorithm (unpack)
open NumberedWindowInternalSparseScalarEdge (packedEdge edge4)
open NumberedWindowInternalSparseScalarEdgeTargets (ActualTermExchange)
open NumberedWindowInternalSparseTypedRawTargets (ActualPackedWindow)
open NumberedWindowInternalSparseScalarEdgeNumericProof (calibration)
open NumberedWindowInternalSparseDirectedRoundsTargets (exactEdgeBit)
open NumberedWindowInternalLiteralPackedLeastOnProof (ActualPackedEdgeOn)
open NumberedWindowInternalLiteralEnrichedEdgeProof
open NumberedWindowInternalLiteralRoundObserverTargets (Preserves)

/-- Complete Boolean fit includes rejection of a malformed context.
This is separate from the open logical content of any edge. -/
def WholeEdgeFit (s : Settings) (E : Program 4) : Prop :=
  exactEdgeBit E = packedEdge s

def EdgeValueStable (s : Settings) (O : Program 3) : Prop :=
  ∀ (ctx ty a b : Nat) (g : List Nat), unpack ctx = some g → edge s g ty a b = true →
    evaluate O (ctx ::ᵥ ty ::ᵥ a ::ᵥ nil) = evaluate O (ctx ::ᵥ ty ::ᵥ b ::ᵥ nil)

theorem exact_WholeOriginalEdge (s : Settings) (X : Program 2) (W : Program 3)
    (xFit : ActualTermExchange s X) (wFit : ActualPackedWindow s W) : WholeEdgeFit s (edge4 X W) := by
  funext ctx ty a b
  unfold exactEdgeBit
  rw [calibration s X W xFit wFit ctx ty a b]
  cases packedEdge s ctx ty a b <;> rfl

theorem exact_PackedEdgeFromWhole (s : Settings) (E : Program 4) (fit : WholeEdgeFit s E) :
    ActualPackedEdgeOn s E := by
  intro ctx ty g decoded
  rw [show exactEdgeBit E = packedEdge s from fit]
  funext a b
  simp [packedEdge,decoded]

theorem exact_WholeEnrichedEdge (s : Settings) (E : Program 4) (O : Program 3)
    (fit : WholeEdgeFit s E) (stable : EdgeValueStable s O) : WholeEdgeFit s (enrichedEdge E O) := by
  unfold WholeEdgeFit at *
  rw [exact_EnrichedEdgeBit]
  · exact fit
  · intro ctx ty a b yes
    rw [fit] at yes
    cases decoded : unpack ctx with
    | none => simp [packedEdge,decoded] at yes
    | some g =>
      apply stable ctx ty a b g decoded
      simpa [packedEdge,decoded] using yes

/-- Earlier observer proofs remain available after additional physical
comparisons are added. The first conjunct is opened explicitly. -/
theorem exact_OpenEnrichmentRetainsObserver (E : Program 4) (O P : Program 3)
    (sound : Preserves E O) : Preserves (enrichedEdge E P) O := by
  intro B α Γ ctx ty a b out edge observed
  exact sound B α Γ ctx ty a b out (exact_OpenEnrichedEdgeBase E P ctx ty a b edge) observed

#print axioms exact_WholeOriginalEdge
#print axioms exact_PackedEdgeFromWhole
#print axioms exact_WholeEnrichedEdge
#print axioms exact_OpenEnrichmentRetainsObserver
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralEdgeObserverFitProof
