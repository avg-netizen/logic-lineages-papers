module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedRoundsTargets
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecEvaluationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestEvaluationProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedRoundsNumericTapeProof
open LogicLineages.OrdinalComparison.TerminationOrdering
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalListCodec (consCode)
open ID1Completion.InternalListCodecEvaluationProof (consEvaluation)
open ID1Completion.InternalEqualityTestEvaluationProof (vectorTwo)
open NumberedMultisetNumeric (numbersNumber)
open NumberedWindowInternalSparseDirectedFilter (pass passTape)
open NumberedWindowInternalSparseDirectedRounds

theorem vectorFour (f : Fin 4 → Nat) :
    List.Vector.ofFn f = f 0 ::ᵥ f 1 ::ᵥ f 2 ::ᵥ f 3 ::ᵥ nil := by
  apply List.Vector.ext
  intro i
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => Fin.cases ?_
    (fun l => Fin.cases ?_ (fun x => Fin.elim0 x) l) k) j) i <;> simp <;> rfl

theorem vectorFive (f : Fin 5 → Nat) :
    List.Vector.ofFn f = f 0 ::ᵥ f 1 ::ᵥ f 2 ::ᵥ f 3 ::ᵥ f 4 ::ᵥ nil := by
  apply List.Vector.ext
  intro i
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => Fin.cases ?_
    (fun l => Fin.cases ?_ (fun x => Fin.cases ?_ (fun y => Fin.elim0 y) x) l) k) j) i <;> simp <;> rfl

private theorem singletonValue (vertices ctx ty seed : Nat) :
    evaluate singletonSeed (vertices ::ᵥ ctx ::ᵥ ty ::ᵥ seed ::ᵥ nil) =
      numbersNumber [seed] := by
  change evaluate consCode (List.Vector.ofFn ![seed, (0 : Nat)]) = _
  rw [vectorTwo]
  exact consEvaluation seed 0

/-- An actual standard scratch singleton, not an extra inserted vertex. -/
theorem baseTape (vertices ctx ty seed : Nat) :
    evaluate roundBase (vertices ::ᵥ ctx ::ᵥ ty ::ᵥ seed ::ᵥ nil) =
      evaluate (pass (constantZero 4))
        (List.Vector.ofFn (passTape vertices (numbersNumber [seed]) ctx ty)) := by
  change evaluate (pass (constantZero 4)) (List.Vector.ofFn
    (passTape vertices (evaluate singletonSeed (vertices ::ᵥ ctx ::ᵥ ty ::ᵥ seed ::ᵥ nil))
      ctx ty)) = _
  rw [singletonValue]

/-- Preserve the original vertex tape and feed the real prior result as seen. -/
theorem stepTape (E : Program 4) (counter prior vertices ctx ty seed : Nat) :
    evaluate (roundStep E) (counter ::ᵥ prior ::ᵥ vertices ::ᵥ ctx ::ᵥ ty ::ᵥ seed ::ᵥ nil) =
      evaluate (pass E) (List.Vector.ofFn (passTape vertices prior ctx ty)) := by
  simp only [vectorFour] <;> rfl

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedRoundsNumericTapeProof
