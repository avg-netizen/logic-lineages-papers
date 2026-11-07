module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaApplicationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ApplicationResultBuilder
open Source

/-- The original function and argument Object decoders, original same-Gamma
restriction and original decoded payload application. The successful payload
is returned with that same Gamma by the original object encoder. -/
def resultOption (n : Nat) (arity : Fin n → Nat) (v : List.Vector Nat 5) : Option Nat := do
  let f ← Encodable.decode (α := ContextUniform.Object) (v.get 3)
  let a ← Encodable.decode (α := ContextUniform.Object) (v.get 4)
  if f.1 = a.1 then
    (OrdinaryArithmeticApplication.decodedApplication n arity f.1
      (v.get 0) (v.get 1) (v.get 2) f.2 a.2).map (ContextUniform.objectCode f.1)
  else none

/-- A total result builder. Zero is only a default, never a success assertion. -/
def resultValue (n : Nat) (arity : Fin n → Nat) (v : List.Vector Nat 5) : Nat :=
  (resultOption n arity v).getD 0

/-- Success must be checked separately, including when the result code is zero. -/
def successValue (n : Nat) (arity : Fin n → Nat) (v : List.Vector Nat 5) : Nat :=
  (resultOption n arity v).isSome.toNat

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ApplicationResultBuilder
