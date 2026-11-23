module
public import Init

@[expose] public section
namespace LogicLineages.PersistentMarking.NativeTowerTypeCodeTargets

def codecPair (a b : Nat) : Nat := (a+b)*(a+b)+a

/-- Literal arithmetic recurrence shared by the rank-free source bridge
and the independent effectivity proof. -/
def typeCode : Nat → Nat :=
  Nat.rec 1 (fun _ old => codecPair old old + 1)

end LogicLineages.PersistentMarking.NativeTowerTypeCodeTargets
