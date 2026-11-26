module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowPrimaryCoverSyntax
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowPrimary

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowPrimaryCoverTargets
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowPrimary
open NumberedWindowHeadEnumerationTargets NumberedWindowPrimaryCoverSyntax

def PrimaryBounds : Prop :=
  (∀ S K C τ Q R, Primary S K C τ Q R → termBounds Q = termBounds R) ∧
  (∀ S K C types qs rs, OrderedPrimary S K C types qs rs → argsBounds qs = argsBounds rs)

def TermGrammarCoverage : Prop :=
  ∀ S K C τ Q m n, InWindow S K C τ Q →
    (termBounds Q).numeral ≤ m → (termBounds Q).nodes ≤ n →
    Q ∈ (grammar (admittedHeads S K) K m n).1

def ArgsGrammarCoverage : Prop :=
  ∀ S K qs m n,
    (∀ σ, σ ∈ argsSupport qs → σ ∈ K) →
    (∀ f, f ∈ argsHeads qs → HeadInWindow S K f) →
    (argsBounds qs).numeral ≤ m → (argsBounds qs).nodes ≤ n →
    qs ∈ (grammar (admittedHeads S K) K m n).2

/-- Both the source and all its entire actual primary class are covered.
The target term has no independent membership, guard or size premise;
those are consequences of the actual typed primary relation in K. -/
def FinitePrimaryClassCover : Prop :=
  ∀ S K C τ Q R, DecisionSourceUniverse.Closed K →
    InWindow S K C τ Q → Primary S K C τ Q R → R ∈ cover S K Q

end LogicLineages.PersistentMarking.NumberedWindowPrimaryCoverTargets
