module
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealContextDefinitions
public import LogicLineages.ModelsAlgebra.Forests.ProfileLanguageEmptyDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.RankedIdealCompletion
open RankedParse ProfileAutomatonEncoding ProfileLanguageEmpty

def productive (M : Machine) [DecidableEq M.State] : Finset M.State :=
  reachable M (Fintype.card M.State)

/-- Only transitions with two genuinely productive children generate diving edges. -/
def Epsilon (M : Machine) [DecidableEq M.State] (x y : M.State) : Prop :=
  x ∈ productive M ∧ ∃ o z, z ∈ productive M ∧
    (y = M.node o x z ∨ y = M.node o z x)

/-- Finite productive trim of the original machine followed by diving epsilon edges.
This inductive run semantics does not define recognition by a superterm oracle. -/
inductive Run (M : Machine) [DecidableEq M.State] : Term → M.State → Prop where
  | atom : Run M .atom M.leaf
  | node {l r x y} (o) : Run M l x → Run M r y →
      x ∈ productive M → y ∈ productive M → Run M (.node o l r) (M.node o x y)
  | epsilon {t x y} : Run M t x → Epsilon M x y → Run M t y

def Accepts (M : Machine) [DecidableEq M.State] (t : Term) : Prop :=
  ∃ q, Run M t q ∧ M.accept q = true
end LogicLineages.ModelsAlgebra.Forests.RankedIdealCompletion
