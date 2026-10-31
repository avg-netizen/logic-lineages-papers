module
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Fintype.Basic

/-! Abstract finite hereditary-cover argument in repaired paper 03,
`decision.tex`, Lemma `lem:image-cover`. These relation-level statements
are suppliers, not a replacement for constructing the actual graph images. -/
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.FiniteIdealCover

def JEP {α : Type} (R : α → α → Prop) (K : α → Prop) : Prop :=
  ∀ a b, K a → K b → ∃ c, K c ∧ R a c ∧ R b c

def Hereditary {α : Type} (R : α → α → Prop) (D : α → Prop) : Prop :=
  ∀ a b, R a b → D b → D a

end LogicLineages.ModelsAlgebra.Forests.FiniteIdealCover
