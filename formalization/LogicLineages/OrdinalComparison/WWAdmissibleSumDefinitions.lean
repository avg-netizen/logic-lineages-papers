module
public import LogicLineages.OrdinalComparison.WWLiteralSizeDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.AdmissibleSum

/-- An ordered full binary addition shape, indexed by its number of leaves.
It cannot inspect or rearrange operands and has no empty/normalizing node. -/
inductive Shape : Nat → Type where
  | leaf : Shape 1
  | join {n m : Nat} : Shape n → Shape m → Shape (n + m)

/-- Instantiate leaves in their original order. Every operand is inserted as
one unchanged subtree, regardless of its syntax, names or denotation. -/
def expand {Γ : List Ty} {n : Nat} (s : Shape n)
    (xs : Fin n → OrdinalExpression Γ) : OrdinalExpression Γ :=
  match s with
  | .leaf => xs 0
  | @Shape.join n m a b => .add
      (expand a (fun i => xs (Fin.castAdd m i)))
      (expand b (fun i => xs (Fin.natAdd n i)))

/-- Operand trace records inserted subtrees, not a flattening of their
internal Add nodes. -/
def operands {Γ : List Ty} {n : Nat} (s : Shape n)
    (xs : Fin n → OrdinalExpression Γ) : List (OrdinalExpression Γ) :=
  match s with
  | .leaf => [xs 0]
  | @Shape.join n m a b =>
      operands a (fun i => xs (Fin.castAdd m i)) ++
      operands b (fun i => xs (Fin.natAdd n i))

inductive MacroSite where
  | numeral | positiveRepeat | activeAdd | activeExp
  | positiveAbstraction | scalarRepeat | optionalBoxTail
  deriving DecidableEq

/-- Structural part of a source-admissible policy. Choice depends only on
macro site and arity. This type by itself asserts neither computability of
an arbitrary selector nor a historical uniqueness convention. -/
structure Policy where
  shape : MacroSite → (n : Nat) → Shape (n + 1)

end LogicLineages.OrdinalComparison.Source.AdmissibleSum
