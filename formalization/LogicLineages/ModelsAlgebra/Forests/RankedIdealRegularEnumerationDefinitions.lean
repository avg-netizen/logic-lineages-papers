module
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealRegularDefinitions
public import Mathlib.Data.List.Pi
public import Mathlib.Data.List.FinRange
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.RankedIdealRegularEnumeration

def pairs {α β : Type} (xs : List α) (ys : List β) : List (α × β) :=
  xs.flatMap (fun x => ys.map (fun y => (x,y)))

def sets {α : Type} [DecidableEq α] : List α → List (Finset α)
  | [] => [∅]
  | x :: xs => sets xs ++ (sets xs).map (insert x)

def functions {n : Nat} {α : Fin n → Type} (xs : ∀ i, List (α i)) : List (∀ i, α i) :=
  (List.pi (List.finRange n) xs).map (fun f i => f i (List.mem_finRange i))
end LogicLineages.ModelsAlgebra.Forests.RankedIdealRegularEnumeration
