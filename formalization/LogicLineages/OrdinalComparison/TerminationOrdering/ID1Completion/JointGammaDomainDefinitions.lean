module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaTypedDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaDomain
open Source

/-- Equality of decoded ambient contexts, using the ORIGINAL Object decoder. -/
def sameContext (f a : Nat) : Prop :=
  ∃ (Gamma : List Ty) (x y : Nat),
    Encodable.decode (α := ContextUniform.Object) f = some (Gamma,x) ∧
    Encodable.decode (α := ContextUniform.Object) a = some (Gamma,y)

def guardValue (v : List.Vector Nat 2) : Nat :=
  match Encodable.decode (α := ContextUniform.Object) (v.get 0),
      Encodable.decode (α := ContextUniform.Object) (v.get 1) with
  | some f, some a => (decide (f.1 = a.1)).toNat
  | _, _ => 0

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaDomain
