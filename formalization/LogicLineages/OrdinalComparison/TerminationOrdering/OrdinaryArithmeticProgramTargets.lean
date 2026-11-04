module

public import LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticProgramDefinitions

@[expose] public section

namespace LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticProgramTargets

open OrdinaryArithmetic
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

def ProgramGraphTruth : Prop := ∀ {n : Nat} (p : Program n) (v : Fin (n + 1) → Nat),
  (graphFormula p).Realize v ↔ evaluate p (List.Vector.ofFn (fun i => v i.succ)) = v 0

def VectorProgramGraphTruth : Prop := ∀ {n : Nat} (p : Program n)
  (inputs : List.Vector Nat n) (out : Nat),
  (graphFormula p).Realize (Fin.cons out inputs.get) ↔ evaluate p inputs = out

def AppliedProgramGraphTruth : Prop := ∀ {n : Nat} {α : Type} (p : Program n)
  (out : Term α) (inputs : Fin n → Term α) (v : α → Nat),
  (applyGraph (graphFormula p) out inputs).Realize v ↔
    evaluate p (List.Vector.ofFn (fun i => (inputs i).realize v)) = out.realize v

def AllPrimitiveGraphs : Prop := ∀ n (f : List.Vector Nat n → Nat), Primrec f →
  ∃ phi : Formula (Fin (n + 1)), ∀ v : Fin (n + 1) → Nat,
    phi.Realize v ↔ f (List.Vector.ofFn (fun i => v i.succ)) = v 0

end LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticProgramTargets
