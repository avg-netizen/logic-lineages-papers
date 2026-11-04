module

public import LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticProgramTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticRecursionProof
public import LogicLineages.ComputabilityKnowledge.GorbowPRProgramProof

@[expose] public section

namespace LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticProgramProof

open FirstOrder Language OrdinaryArithmetic OrdinaryArithmeticProgramTargets
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem programGraphTruth {n : Nat} (p : Program n) (v : Fin (n + 1) → Nat) :
    (graphFormula p).Realize v ↔ evaluate p (List.Vector.ofFn (fun i => v i.succ)) = v 0 := by
  induction p with
  | zero => simp [graphFormula, OrdinaryArithmeticBetaProof.realize_zero, evaluate]
  | succ => simp [graphFormula, OrdinaryArithmeticBetaProof.realize_succ, evaluate]
  | projection i => simp [graphFormula, evaluate]
  | composition f g hf hg =>
    exact OrdinaryArithmeticCompositionProof.actualCompositionGraph f g
      (graphFormula f) (fun i => graphFormula (g i)) hf hg v
  | recursion f g hf hg =>
    exact OrdinaryArithmeticRecursionProof.actualRecursionGraph f g
      (graphFormula f) (graphFormula g) hf hg v

theorem vectorProgramGraphTruth : VectorProgramGraphTruth := by
  intro n p inputs out
  simpa only [Fin.cons_zero, Fin.cons_succ, List.Vector.ofFn_get] using
    programGraphTruth p (Fin.cons out inputs.get)

theorem appliedProgramGraphTruth : AppliedProgramGraphTruth := by
  intro n α p out inputs v
  rw [OrdinaryArithmeticCompositionProof.applyGraphTruth, programGraphTruth]
  simp only [Fin.cons_zero, Fin.cons_succ]

theorem allPrimitiveGraphs : AllPrimitiveGraphs := by
  intro n f hf
  obtain ⟨p, hp⟩ := Proof.allPrimitiveFunctions n f hf
  refine ⟨graphFormula p, ?_⟩
  intro v
  rw [programGraphTruth, hp]

end LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticProgramProof
