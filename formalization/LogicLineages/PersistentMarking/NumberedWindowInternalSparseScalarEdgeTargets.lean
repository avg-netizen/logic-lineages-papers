module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScalarEdgeDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseScalarEdgeTargets
open LogicLineages.OrdinalComparison.TerminationOrdering
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparseTypedRawTargets (ActualPackedWindow)
open NumberedWindowInternalSparseDirectedSeen (edgeTape)
open NumberedWindowInternalSparseScalarEdge

/-- The actual guarded-syntax contextual exchange term bit for fixed
original equivalent-head pairs, in directed source/destination order. -/
def ActualTermExchange (s : Settings) (X : Program 2) : Prop :=
  ∀ w v : Nat, evaluate X (List.Vector.ofFn (exchangeTape w v)) =
    ((NumberedWindowExchangeAlgorithm.bits s.equivalentHeads w v).1).toNat

def ActualPackedScalarEdge (s : Settings) (E : Program 4) : Prop :=
  ∀ ctx ty w v : Nat, evaluate E (List.Vector.ofFn (edgeTape ctx ty w v)) =
    (packedEdge s ctx ty w v).toNat

/-- All raw natural inputs at the actual single packed context. The
physical wrapper is calibrated only by the two original named callbacks. -/
def ExactPackedScalarEdgeCalibration : Prop :=
  ∀ (s : Settings) (X : Program 2) (W : Program 3),
    ActualTermExchange s X → ActualPackedWindow s W → ActualPackedScalarEdge s (edge4 X W)

/-- Choose the actual callbacks at the very same Settings and retain
the exact same composed E, not a third existential edge program. -/
def ExactSelectedPackedScalarEdge : Prop :=
  ∀ s : Settings, ∃ (X : Program 2) (W : Program 3),
    ActualTermExchange s X ∧ ActualPackedWindow s W ∧ ActualPackedScalarEdge s (edge4 X W)

/-- Literal graphs only: both directions use the same physical X/W at
the same tapes in arbitrary object context and body. No numerical
calibration or internal exchange-table semantics is a premise or conclusion. -/
def ExactOpenPackedScalarEdge : Prop :=
  ∀ (X : Program 2) (W : Program 3) (body : Positive (Fin 1)) (α : Type)
    (Γ : List (Formula α)) (ctx ty w v : OTerm α),
    let accepted := edgeGraph X W ctx ty w v
    let calls := edgeCalls X W ctx ty w v
    Nonempty (Derivation body Γ ((accepted.imp calls) ⊓ (calls.imp accepted)))

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseScalarEdgeTargets
