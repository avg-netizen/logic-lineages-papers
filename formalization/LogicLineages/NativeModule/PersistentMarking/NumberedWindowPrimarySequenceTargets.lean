module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowPrimarySequence

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowPrimarySequenceTargets
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowPrimary
open NumberedWindowPrimarySequence

def TypedElementarySound : Prop :=
  (∀ S K C τ Q R, TypedExchange S K C τ Q R → Primary S K C τ Q R) ∧
  (∀ S K C types qs rs, TypedArgsExchange S K C types qs rs →
    OrderedPrimary S K C types qs rs)

def ExactTypedPrimarySequences : Prop := ∀ S K C τ Q R,
  Primary S K C τ Q R ↔ Nonempty (TypedExchangeTrace S K C τ Q R)

def ExactTypedOrderedSequences : Prop := ∀ S K C types qs rs,
  OrderedPrimary S K C types qs rs ↔ Nonempty (TypedArgsExchangeTrace S K C types qs rs)

/-- Every vertex of the supplied concrete typed sequence is admitted from
its INITIAL guard alone. The resulting admitted sequence has exactly
the same visited vertices, including repeated or final positions. -/
def ActualSequenceWindowPropagation : Prop :=
  ∀ S K C τ Q R (trace : TypedExchangeTrace S K C τ Q R),
    DecisionSourceUniverse.Closed K → InWindow S K C τ Q →
      (∀ T, T ∈ typedVertices trace → InWindow S K C τ T) ∧
      ∃ admitted : AdmittedExchangeTrace S K C τ Q R, admittedVertices admitted = typedVertices trace

def ExactAdmittedPrimarySequences : Prop := ∀ S K C τ Q R,
  DecisionSourceUniverse.Closed K → InWindow S K C τ Q →
    (Primary S K C τ Q R ↔ Nonempty (AdmittedExchangeTrace S K C τ Q R))

end LogicLineages.PersistentMarking.NumberedWindowPrimarySequenceTargets
