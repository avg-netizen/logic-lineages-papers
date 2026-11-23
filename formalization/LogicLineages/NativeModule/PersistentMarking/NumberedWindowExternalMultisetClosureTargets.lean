module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowExternalIDOperators

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowExternalMultisetClosureTargets
open NumberedWindowExternalIDOperators NumberedWindowArithmeticFields

/-- Multiset union of two members of the external numeral-coded J predicate. -/
def ExternalJUnion : Prop :=
  ∀ S K (left right : List Nat),
    Least (multisetStep S K) (encodeFields left) →
    Least (multisetStep S K) (encodeFields right) →
    Least (multisetStep S K) (encodeFields (left ++ right))

/-- A member of the external scalar I predicate gives a singleton in J. -/
def ExternalISingleton : Prop :=
  ∀ S K a, Least (scalarStep S K) a → Least (multisetStep S K) (encodeFields [a])

/-- Every finite multiset of external I-members belongs to the actual external J. -/
def ExternalIFiniteMultiset : Prop :=
  ∀ S K (xs : List Nat), (∀ a ∈ xs, Least (scalarStep S K) a) →
    Least (multisetStep S K) (encodeFields xs)

end LogicLineages.PersistentMarking.NumberedWindowExternalMultisetClosureTargets
