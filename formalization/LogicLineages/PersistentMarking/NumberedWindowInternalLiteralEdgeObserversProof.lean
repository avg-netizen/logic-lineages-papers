module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralEdgeObserverFitProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralEdgeOnCoverProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralEdgeObserversProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalLiteralRoundObserverTargets (Preserves)
open NumberedWindowInternalLiteralEnrichedEdgeProof
open NumberedWindowInternalLiteralEdgeObserverFitProof
open NumberedWindowInternalLiteralEnrichedEdgeReversalProof
open NumberedWindowInternalLiteralEdgeOnCoverProof

/-- From left to right, every comparison is installed in the actual
finite edge. The underlying four slots never change. -/
def withObservers (E : Program 4) : List (Program 3) → Program 4
  | [] => E
  | O :: tail => enrichedEdge (withObservers E tail) O

theorem exact_OpenRetainedObserver (E : Program 4) (O : Program 3)
    (stable : Preserves E O) (more : List (Program 3)) : Preserves (withObservers E more) O := by
  induction more with
  | nil => exact stable
  | cons p tail ih => exact exact_OpenEnrichmentRetainsObserver (withObservers E tail) O p ih

theorem exact_OpenInstalledObserver (E : Program 4) (ss : List (Program 3)) (O : Program 3)
    (member : O ∈ ss) : Preserves (withObservers E ss) O := by
  induction ss with
  | nil => simp at member
  | cons p tail ih =>
    rcases List.mem_cons.mp member with rfl | inTail
    · exact exact_OpenEnrichedEdgeObservation (withObservers E tail) O
    · exact exact_OpenEnrichmentRetainsObserver (withObservers E tail) O p (ih inTail)

theorem exact_WholeEdgeWithObservers (s : Settings) (E : Program 4) (ss : List (Program 3))
    (fit : WholeEdgeFit s E) (stable : ∀ O ∈ ss, EdgeValueStable s O) : WholeEdgeFit s (withObservers E ss) := by
  induction ss with
  | nil => exact fit
  | cons p tail ih =>
    exact exact_WholeEnrichedEdge s (withObservers E tail) p (ih (fun O h => stable O (List.mem_cons_of_mem _ h)))
      (stable p List.mem_cons_self)

theorem exact_OpenEdgeWithObserversReverses (E : Program 4) (ss : List (Program 3))
    (reverses : CanReverse E) : CanReverse (withObservers E ss) := by
  induction ss with
  | nil => exact reverses
  | cons p tail ih => exact exact_OpenEnrichedEdgeReverses (withObservers E tail) p ih

theorem exact_OpenEdgeWithObserversCover (C : Program 3) (s : Settings) (E : Program 4)
    (ss : List (Program 3)) (cover : KeepsCover C s E) : KeepsCover C s (withObservers E ss) := by
  induction ss with
  | nil => exact cover
  | cons p tail ih => exact exact_OpenEnrichedEdgeCover C s (withObservers E tail) p ih

#print axioms exact_OpenInstalledObserver
#print axioms exact_WholeEdgeWithObservers
#print axioms exact_OpenEdgeWithObserversReverses
#print axioms exact_OpenEdgeWithObserversCover
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralEdgeObserversProof
