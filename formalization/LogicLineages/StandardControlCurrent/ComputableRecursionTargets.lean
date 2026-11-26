module
public import Mathlib.Computability.Primrec.List
public import Mathlib.Computability.Partrec

@[expose] public section
namespace LogicLineages.StandardControlCurrent.ComputableRecursionTargets

/-- Supporting traversal with merely computable, not primitive recursive, steps. -/
def ListFold : Prop :=
  ∀ (α β σ : Type) [Primcodable α] [Primcodable β] [Primcodable σ]
    (xs : α → List β) (initial : α → σ) (step : α → σ → β → σ),
    Computable xs → Computable initial →
    Computable (fun p : α × σ × β => step p.1 p.2.1 p.2.2) →
    Computable (fun a => (xs a).foldl (step a) (initial a))

/-- A total literal recursion equation over actual decreasing finite child lists.
The assembly program may be merely computable, as required by arbitrary policies. -/
def RankedRecursion : Prop :=
  ∀ (β σ : Type) [Primcodable β] [Primcodable σ]
    (f : β → σ) (rank : β → Nat) (children : β → List β)
    (assemble : β → List σ → Option σ),
    Primrec rank → Primrec children →
    Computable (fun p : β × List σ => assemble p.1 p.2) →
    (∀ b, ∀ c ∈ children b, rank c < rank b) →
    (∀ b, assemble b ((children b).map f) = some (f b)) → Computable f

def Full : Prop := ListFold ∧ RankedRecursion
end LogicLineages.StandardControlCurrent.ComputableRecursionTargets
