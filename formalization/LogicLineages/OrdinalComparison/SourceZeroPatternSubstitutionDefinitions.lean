module
public import LogicLineages.OrdinalComparison.SourceFiniteExponentProjectionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceZeroPatternSubstitution
noncomputable def lookup {n m : Nat} (r : Fin m → Fin n) (i : Fin n) : Option (Fin m) :=
  if h : ∃ j,r j=i then some (Classical.choose h) else none
def zeroExpression (m : Nat) : SignedPair.Expression m := .add .unit (.neg .unit)
noncomputable def substitute {n m : Nat} (r : Fin m → Fin n) :
    SignedPair.Expression n → SignedPair.Expression m
  | .unit => .unit
  | .var i => match lookup r i with | none => zeroExpression m | some j => .var j
  | .add a b => .add (substitute r a) (substitute r b)
  | .neg a => .neg (substitute r a)
  | .shift a => .shift (substitute r a)
noncomputable def extend {n m : Nat} {A : Type*} [Zero A]
    (r : Fin m → Fin n) (x : Fin m → A) (i : Fin n) : A :=
  match lookup r i with | none => 0 | some j => x j
end LogicLineages.OrdinalComparison.Source.SourceZeroPatternSubstitution
