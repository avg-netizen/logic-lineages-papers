module

public import LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticCompositionDefinitions

@[expose] public section

namespace LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticCompositionTargets

open OrdinaryArithmetic
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

def ExistsFiniteTruth : Prop := ∀ {α : Type} {k : Nat}
  (p : Formula (α ⊕ Fin k)) (v : α → Nat),
  (existsFin p).Realize v ↔ ∃ xs : Fin k → Nat, p.Realize (Sum.elim v xs)

def ForallFiniteTruth : Prop := ∀ {α : Type} {k : Nat}
  (p : Formula (α ⊕ Fin k)) (v : α → Nat),
  (forallFin p).Realize v ↔ ∀ xs : Fin k → Nat, p.Realize (Sum.elim v xs)

def ApplyGraphTruth : Prop := ∀ {n : Nat} {α : Type}
  (p : Formula (Fin (n + 1))) (out : Term α) (inputs : Fin n → Term α) (v : α → Nat),
  (applyGraph p out inputs).Realize v ↔
    p.Realize (Fin.cons (out.realize v) (fun i => (inputs i).realize v))

def FiniteConjunctionTruth : Prop := ∀ {α : Type} {n : Nat}
  (p : Fin n → Formula α) (v : α → Nat),
  (andFin p).Realize v ↔ ∀ i, (p i).Realize v

def LessTruth : Prop := ∀ {α : Type} (s t : Term α) (v : α → Nat),
  (lessFormula s t).Realize v ↔ s.realize v < t.realize v

/-- Actual Program composition, conditional only on the two displayed child
graph specifications. A structural compiler will discharge these by induction. -/
def ActualCompositionGraph : Prop := ∀ {m n : Nat} (f : Program n)
  (g : Fin n → Program m) (F : Formula (Fin (n + 1)))
  (G : Fin n → Formula (Fin (m + 1))),
  (∀ v : Fin (n + 1) → Nat,
    F.Realize v ↔ evaluate f (List.Vector.ofFn (fun i => v i.succ)) = v 0) →
  (∀ i (v : Fin (m + 1) → Nat),
    (G i).Realize v ↔ evaluate (g i) (List.Vector.ofFn (fun j => v j.succ)) = v 0) →
  ∀ v : Fin (m + 1) → Nat,
    (compositionGraph F G).Realize v ↔
      evaluate (.composition f g) (List.Vector.ofFn (fun i => v i.succ)) = v 0

end LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticCompositionTargets
