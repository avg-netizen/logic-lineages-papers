module

public import LogicLineages.NativeModule.PersistentMarking.MarkedConstructorTargets

@[expose] public section

namespace LogicLineages.PersistentMarking.MarkedConstructorOperator
open Spine DecisionInventory FiniteDomainSchema HereditaryDomainCode

def environment (s t : Expr) : Environment :=
  let I := inventory s t
  ⟨I.types,I.names,I.ports,t⟩

/-- Encode the new marked value at every actual family coordinate. -/
def nextFamily (S : Signature) (E : Environment) (heads : List Head) (M : Code) :
    MarkedFamilyCoding.Family :=
  fun p => HereditaryDomainSemantics.encode E p.2.1 p.2.2.1
    (MarkedConstructorValue.build S E heads M p)

def step (S : Signature) (E : Environment) (heads : List Head) (M : Code) : Code :=
  (MarkedFamilyCoding.encode E heads (nextFamily S E heads M)).getD []

def iterate (S : Signature) (E : Environment) (heads : List Head) : Nat → Code
  | 0 => MarkedFamilyLattice.join E heads []
  | n+1 => step S E heads (iterate S E heads n)

def leastFixedPoint (S : Signature) (E : Environment) (heads : List Head) : Code :=
  iterate S E heads (MarkedFamilyCoherence.retained E heads).length

end LogicLineages.PersistentMarking.MarkedConstructorOperator
