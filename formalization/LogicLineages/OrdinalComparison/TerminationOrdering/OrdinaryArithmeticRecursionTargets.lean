module

public import LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticRecursionDefinitions

@[expose] public section

namespace LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticRecursionTargets

open OrdinaryArithmetic
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

def InitialGraphTruth : Prop := ∀ {n : Nat} {α : Type}
  (f : Formula (Fin (n + 1))) (a b : Term α) (params : Fin n → Term α) (v : α → Nat),
  (initialGraph f a b params).Realize v ↔
    f.Realize (Fin.cons (a.realize v % (b.realize v + 1))
      (fun i => (params i).realize v))

def StepGraphTruth : Prop := ∀ {n : Nat} {α : Type}
  (g : Formula (Fin (n + 3))) (a b t : Term α) (params : Fin n → Term α) (v : α → Nat),
  (stepGraph g a b t params).Realize v ↔
    ∀ j : Nat, j < t.realize v →
      g.Realize (Fin.cons (a.realize v % (((j + 1) + 1) * b.realize v + 1))
        (Fin.cons j (Fin.cons (a.realize v % ((j + 1) * b.realize v + 1))
          (fun i => (params i).realize v))))

def ActualRecursionGraph : Prop := ∀ {n : Nat} (f : Program n) (g : Program (n + 2))
  (F : Formula (Fin (n + 1))) (G : Formula (Fin (n + 3))),
  (∀ v : Fin (n + 1) → Nat,
    F.Realize v ↔ evaluate f (List.Vector.ofFn (fun i => v i.succ)) = v 0) →
  (∀ v : Fin (n + 3) → Nat,
    G.Realize v ↔ evaluate g (List.Vector.ofFn (fun i => v i.succ)) = v 0) →
  ∀ v : Fin (n + 2) → Nat,
    (recursionGraph F G).Realize v ↔
      evaluate (.recursion f g) (List.Vector.ofFn (fun i => v i.succ)) = v 0

end LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticRecursionTargets
