module
public import LogicLineages.OrdinalComparison.SourceCollisionCompletionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceAggregateCompletion
open SourceCollisionCompletion

/-- Explicit finite source construction. Both outputs use the same eraser
shape; each leaf pair is the actual six-eraser detector. Empty conjunctions
produce the literal source zero twice. No source variable is replaced. -/
def aggregate {Γ : List Ty} :
    List (OriginalTerm Γ .ground × OriginalTerm Γ .ground) →
      OriginalTerm Γ .ground × OriginalTerm Γ .ground
  | [] => (.zeroC, .zeroC)
  | (p,q) :: es =>
    let tail := aggregate es
    (eraser (detectorLeft p q) tail.1, eraser (detectorRight p q) tail.2)

def AllEqual {Γ : List Ty} (ν : OrdinalComponent Γ → Ordinal)
    (es : List (OriginalTerm Γ .ground × OriginalTerm Γ .ground)) : Prop :=
  ∀ e ∈ es, rawScalar ν e.1 = rawScalar ν e.2

def AggregateAt {Γ : List Ty} (ν : OrdinalComponent Γ → Ordinal)
    (es : List (OriginalTerm Γ .ground × OriginalTerm Γ .ground)) : Prop :=
  rawScalar ν (aggregate es).2 ≤ rawScalar ν (aggregate es).1 ∧
  (rawScalar ν (aggregate es).1 = rawScalar ν (aggregate es).2 ↔ AllEqual ν es) ∧
  (¬ AllEqual ν es → 2 ≤ rawScalar ν (aggregate es).1 - rawScalar ν (aggregate es).2)
end LogicLineages.OrdinalComparison.Source.SourceAggregateCompletion
