module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticLeastClass

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticLeastClassTargets
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowPrimary NumberedWindowSimulationData
open NumberedWindowArithmeticTermCode NumberedWindowArithmeticLeastClass

def LeastCodeSpecification : Prop :=
  ∀ S K Γ τ Q, DecisionSourceUniverse.Closed K → InWindow S K (finiteC Γ) τ Q →
    ∃ code R, leastCode S K Γ τ Q = some code ∧
      representative S K Γ τ Q = some R ∧ encodeTerm R = code ∧
      InWindow S K (finiteC Γ) τ R ∧ Primary S K (finiteC Γ) τ Q R ∧
      (∀ X, Primary S K (finiteC Γ) τ Q X → code ≤ encodeTerm X) ∧
      (∀ X, Primary S K (finiteC Γ) τ Q X → encodeTerm X = code → X = R)

def LeastCodeReflectsPrimary : Prop :=
  ∀ S K Γ τ Q R, DecisionSourceUniverse.Closed K →
    InWindow S K (finiteC Γ) τ Q → InWindow S K (finiteC Γ) τ R →
      (leastCode S K Γ τ Q = leastCode S K Γ τ R ↔ Primary S K (finiteC Γ) τ Q R)

def RepresentativeReflectsPrimary : Prop :=
  ∀ S K Γ τ Q R, DecisionSourceUniverse.Closed K →
    InWindow S K (finiteC Γ) τ Q → InWindow S K (finiteC Γ) τ R →
      (representative S K Γ τ Q = representative S K Γ τ R ↔
        Primary S K (finiteC Γ) τ Q R)

def LeastCodeReflectsActualQuotient : Prop :=
  ∀ S K Γ τ (Q R : WindowCarrier S K (finiteC Γ) τ), DecisionSourceUniverse.Closed K →
    (leastCode S K Γ τ Q.val = leastCode S K Γ τ R.val ↔ classOf Q = classOf R)

end LogicLineages.PersistentMarking.NumberedWindowArithmeticLeastClassTargets
