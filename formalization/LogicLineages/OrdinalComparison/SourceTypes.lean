module
public import Init.Data.List.Lemmas
public import Init.Data.Nat.Lemmas

@[expose] public section

/-! Literal simple types shared by the Gödel-T source papers. These definitions
contain no ordering-comparison oracle or normalization assumption. -/

namespace LogicLineages.OrdinalComparison.Source

inductive Ty where
  | ground
  | arrow (domain codomain : Ty)
  deriving DecidableEq, Repr

def Ty.level : Ty → Nat
  | .ground => 0
  | .arrow σ τ => max (σ.level + 1) τ.level

/-- A curried list of ground arguments ending at the ground result. -/
def Ty.curriedGround : Nat → Ty
  | 0 => .ground
  | k + 1 => .arrow .ground (curriedGround k)

/-- Literal type-subexpression closure, as an executable finite list. -/
def Ty.subtypes : Ty → List Ty
  | .ground => [.ground]
  | .arrow σ τ => .arrow σ τ :: (σ.subtypes ++ τ.subtypes)

def Ty.caseType (τ : Ty) : Ty := .arrow .ground (.arrow τ (.arrow τ τ))

def Ty.recType (τ : Ty) : Ty :=
  .arrow .ground (.arrow (.arrow .ground (.arrow τ τ)) (.arrow τ τ))

end LogicLineages.OrdinalComparison.Source
