module
public import LogicLineages.OrdinalComparison.UnitEliminationTreeCodeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.UnitEliminationTreeCode.Targets

def ExactTreeFold : Prop := ∀ (α : Type) [Encodable α] (Γ : List Ty) (q : UnitElimination.Tree α Γ)
    (leaf : Nat → Nat) (free : Nat → Nat → Nat) (active : Nat → Nat → Nat → Nat),
  fold leaf free active (code q) = treeFold leaf free active q

def EffectiveConstructorsAndFold : Prop :=
  Primrec leafCode ∧ Primrec₂ freeCode ∧
  Primrec (fun p : Nat×Nat×Nat => activeCode p.1 p.2.1 p.2.2) ∧
  (∀ (leaf : Nat → Nat) (free : Nat → Nat → Nat) (active : Nat → Nat → Nat → Nat),
    Primrec leaf → Primrec₂ free → Primrec (fun p : Nat×Nat×Nat => active p.1 p.2.1 p.2.2) →
    Primrec (fold leaf free active)) ∧
  (∀ (leaf : Nat → Nat) (free : Nat → Nat → Nat) (active : Nat → Nat → Nat → Nat),
    Computable leaf → Computable₂ free → Computable (fun p : Nat×Nat×Nat => active p.1 p.2.1 p.2.2) →
    Computable (fold leaf free active))

/-- Only anchor programs are executed. Every original source/context/factor,
selection field, coefficient, child order and repeated occurrence is retained. -/
def ExactAnchorRealization : Prop := Computable realizeCode ∧
  ∀ (Γ : List Ty) (q : UnitElimination.Tree (Nat×Nat) Γ),
    realizeCode (code q) = code (UnitElimination.realize q)
end LogicLineages.OrdinalComparison.Source.UnitEliminationTreeCode.Targets
