import LogicLineages.PersistentMarking.NumberedWindowExternalComputability
import LogicLineages.PersistentMarking.NumberedWindowExternalNeutralTargets

namespace LogicLineages.PersistentMarking.NumberedWindowExternalTypeFactsTargets
open NumberedWindowSimulationData NumberedWindowArithmeticLeastClass
open NumberedWindowExternalComputability NumberedWindowExternalNeutralTargets
open NumberedWindowExternalIDOperators NumberedWindowPathWitnessTargets
open NumberedWindowArithmeticClassAddress

def VariableClass {S K C τ} (q : Class S K C τ) : Prop :=
  ∃ Q : WindowCarrier S K C τ, (∃ i, Q.val = .free τ i ∨ Q.val = .bound τ i) ∧ classOf Q = q

def NeutralComputability : Prop :=
  ∀ S K Γ τ (hk : DecisionSourceUniverse.Closed K) (q : Class S K (finiteC Γ) τ),
    ClassNonLambda q → (∀ r, ClassEdge q r → ComputableClass S K Γ hk τ r) →
      ComputableClass S K Γ hk τ q

def BottomComputability : Prop :=
  ∀ S K Γ τ (hk : DecisionSourceUniverse.Closed K) (q : Class S K (finiteC Γ) τ),
    ClassBottom q → ComputableClass S K Γ hk τ q

def VariableComputability : Prop :=
  ∀ S K Γ τ (hk : DecisionSourceUniverse.Closed K) (q : Class S K (finiteC Γ) τ),
    VariableClass q → ComputableClass S K Γ hk τ q

def ComputabilityImpliesScalarI : Prop :=
  ∀ S K Γ τ (hk : DecisionSourceUniverse.Closed K) (q : Class S K (finiteC Γ) τ) i,
    ActualCodeAt S K Γ τ i q → ComputableClass S K Γ hk τ q →
      Least (scalarStep S K) (encodeAddress ⟨Γ,τ,i⟩)

end LogicLineages.PersistentMarking.NumberedWindowExternalTypeFactsTargets
