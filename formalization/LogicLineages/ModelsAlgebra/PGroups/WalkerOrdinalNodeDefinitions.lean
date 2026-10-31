module
public import Mathlib.SetTheory.Ordinal.Basic
public import Mathlib.Logic.Equiv.List
public import Mathlib.Data.List.Pairwise
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups

/-- Source nodes (ξ, ξ₁, …, ξₙ), stored as the reversed tail [ξₙ,…,ξ₁]
inside ξ.ToType. Reversing is solely a representation choice: Pairwise (<)
is precisely strict decrease of the source tail, and every entry is below ξ. -/
def WalkerOrdinalNode (ξ : Ordinal) := {s : List ξ.ToType // s.Pairwise (· < ·)}

def walkerOrdinalRoot (ξ : Ordinal) : WalkerOrdinalNode ξ := ⟨[], List.Pairwise.nil⟩

def walkerOrdinalParent (ξ : Ordinal) : WalkerOrdinalNode ξ → Option (WalkerOrdinalNode ξ)
  | ⟨[], _⟩ => none
  | ⟨_ :: l, h⟩ => some ⟨l, h.tail⟩

def walkerOrdinalHeight (ξ : Ordinal) : WalkerOrdinalNode ξ → Ordinal
  | ⟨[], _⟩ => ξ
  | ⟨a :: _, _⟩ => Ordinal.typein (α := ξ.ToType) (· < ·) a

noncomputable def walkerOrdinalCode (ξ : Ordinal) [Countable ξ.ToType]
    (s : WalkerOrdinalNode ξ) : ℕ :=
  letI := Encodable.ofCountable ξ.ToType
  Encodable.encode s.val

end LogicLineages.ModelsAlgebra.PGroups
