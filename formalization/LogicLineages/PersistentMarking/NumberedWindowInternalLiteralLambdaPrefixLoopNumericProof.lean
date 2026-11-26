module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaPrefixStateNumericProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTickNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathAdvanceTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaPrefixLoopNumericProof
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowFieldAlgorithm (unpackNode)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathAdvanceTargets (packedRaw)
open NumberedWindowInternalSparseTypedRawTargets (ActualPackedWindow)
open NumberedWindowInternalSparsePathEnvelope (run)
open NumberedWindowInternalSparseFieldCell (cellHead)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof (vectorOne)

set_option maxHeartbeats 130000
open NumberedWindowInternalLiteralLambdaLexicalGateNumericProof (typedTape)
open NumberedWindowInternalLiteralLambdaPrefixMachineProof
open NumberedWindowInternalLiteralLambdaPrefixStateNumericProof

attribute [local irreducible] prefixTick prefixStart

open NumberedWindowInternalLiteralTickNumericProof (numericIter evalTickLoop)

def prefixIter (W : Program 3) : Nat → Nat → Nat := numericIter (prefixTick W)

theorem prefixIterTerminal (W : Program 3) (fuel flag : Nat) :
    prefixIter W fuel (typedStateCode flag 0) = typedStateCode flag 0 := by
  induction fuel with
  | zero => rfl
  | succ n ih =>
    rw [prefixIter,numericIter,evalPrefixTickTerminal]
    exact ih

theorem evalPrefixLoop (W : Program 3) (fuel x : Nat) :
    evaluate (prefixLoop W) (fuel ::ᵥ x ::ᵥ nil) = prefixIter W fuel x :=
  evalTickLoop (prefixTick W) fuel x

theorem evalPrefixOwn (W : Program 3) (c t q w r : Nat) :
    evaluate (prefixOwn W) (typedTape c t q w r) =
      run cellHead (prefixIter W w (typedStateCode 1 (typedFrameCode c t q w r))) := by
  change evaluate cellHead (List.Vector.ofFn (fun _ : Fin 1 => evaluate (prefixOwnState W)
    (typedTape c t q w r))) = _
  rw [vectorOne,prefixOwnState]
  change run cellHead (evaluate (prefixLoop W) (List.Vector.ofFn (fun i :
    Fin 2 => evaluate ((![.projection 3,prefixStart] : Fin 2 → Program 5) i) (typedTape c t q w r)))) = _
  have rows : (List.Vector.ofFn (fun i : Fin 2 => evaluate
      ((![.projection 3,prefixStart] : Fin 2 → Program 5) i) (typedTape c t q w r))) =
      w ::ᵥ evaluate prefixStart (typedTape c t q w r) ::ᵥ nil := by
    apply List.Vector.ext
    intro i
    exact Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)) i
  rw [rows,evalPrefixStart,evalPrefixLoop]


#print axioms prefixIterTerminal
#print axioms evalPrefixLoop
#print axioms evalPrefixOwn
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaPrefixLoopNumericProof
