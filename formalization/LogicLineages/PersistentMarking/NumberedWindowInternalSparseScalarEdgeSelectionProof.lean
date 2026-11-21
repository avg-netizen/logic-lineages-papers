module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScalarEdgeTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScalarEdgeNumericProof
import LogicLineages.PersistentMarking.NumberedWindowExchangeProgramProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawPackedWindowProof
import LogicLineages.ComputabilityKnowledge.GorbowPRProgramProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestEvaluationProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseScalarEdgeSelectionProof
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalEqualityTestEvaluationProof (vectorTwo)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowExchangeAlgorithm (bits)
open NumberedWindowExchangeProgramProof (bitsPrim)
open NumberedWindowInternalSparseTypedRawPackedWindowProof (packedWindowWitness)
open NumberedWindowInternalSparseScalarEdge
open NumberedWindowInternalSparseScalarEdgeTargets
open NumberedWindowInternalSparseScalarEdgeNumericProof (calibration)

private theorem coordinate (i : Fin 2) :
    Primrec (fun v : List.Vector Nat 2 => v.get i) :=
  Primrec.vector_get.comp Primrec.id (Primrec.const i)

private theorem termBitPrim (s : Settings) :
    Primrec (fun v : List.Vector Nat 2 => (bits s.equivalentHeads (v.get 0) (v.get 1)).1) :=
  Primrec.fst.comp
    (bitsPrim.comp ((Primrec.const s.equivalentHeads).pair ((coordinate 0).pair (coordinate 1))))

/-- Select an actual arity-two term bit, not the encoded term/args pair
or a test with independent endpoint guards. -/
private theorem exchangeWitness (s : Settings) : ∃ X : Program 2, ActualTermExchange s X := by
  let value (v : List.Vector Nat 2) := ((bits s.equivalentHeads (v.get 0) (v.get 1)).1).toNat
  have hv : Primrec value := by
    apply (Primrec.cond (termBitPrim s) (Primrec.const (1 : Nat)) (Primrec.const 0)).of_eq
    intro v
    dsimp only [value]
    cases (bits s.equivalentHeads (v.get 0) (v.get 1)).1 <;> rfl
  obtain ⟨X,hX⟩ := GorbowPRProgram.Proof.allPrimitiveFunctions 2 value hv
  refine ⟨X,?_⟩
  intro w v
  rw [vectorTwo]
  exact hX (w ::ᵥ v ::ᵥ nil)

theorem selected : ExactSelectedPackedScalarEdge := by
  intro s
  obtain ⟨X,hX⟩ := exchangeWitness s
  obtain ⟨W,hW⟩ := packedWindowWitness s
  exact ⟨X,W,hX,hW,calibration s X W hX hW⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseScalarEdgeSelectionProof
