module
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealRegularEnumerationDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.RankedIdealRegularEnumeration.Targets

def PairsComplete : Prop := ∀ {α β : Type} (xs : List α) (ys : List β) x y,
  x ∈ xs → y ∈ ys → (x,y) ∈ pairs xs ys

def SetsExact : Prop := ∀ {α : Type} [DecidableEq α] (xs : List α) (s : Finset α),
  s ∈ sets xs ↔ ∀ x ∈ s, x ∈ xs

def FunctionsComplete : Prop := ∀ n {α : Fin n → Type} (xs : ∀ i, List (α i)) f,
  (∀ i, f i ∈ xs i) → f ∈ functions xs
end LogicLineages.ModelsAlgebra.Forests.RankedIdealRegularEnumeration.Targets
