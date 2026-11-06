module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ContextUniformTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaProgramsTargets

/-- ORIGINAL encoded context/object carrier checker; no validity restriction on inputs. -/
def ActualScalarPrimitive : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat), Primrec (ContextUniform.scalarValue n arity)

/-- ORIGINAL encoded context/object multiset-carrier checker, including its empty-list behavior. -/
def ActualListPrimitive : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat), Primrec (ContextUniform.listValue n arity)

/-- ORIGINAL encoded positive-path checker; unequal ambient contexts still return zero. -/
def ActualPositivePrimitive : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat), Primrec (ContextUniform.positiveValue n arity)

/-- ORIGINAL encoded direct-multiset checker on all four numeric inputs. -/
def ActualDirectPrimitive : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat), Primrec (ContextUniform.directValue n arity)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaProgramsTargets
