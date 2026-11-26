import LogicLineages.PersistentMarking.NumberedWindowExternalComputability

namespace LogicLineages.PersistentMarking.NumberedWindowExternalComputabilityTargets
open NumberedWindowExternalComputability NumberedWindowExternalApplication
open NumberedWindowArithmeticLeastClass NumberedWindowArithmeticClassAddress
open NumberedWindowSimulationData NumberedWindowExternalIDOperators NumberedWindowPathWitnessTargets

def GroundAtCanonicalAddress : Prop :=
  ∀ S K Γ (hk : DecisionSourceUniverse.Closed K) (q : Class S K (finiteC Γ) .ground) i,
    ActualCodeAt S K Γ .ground i q →
    (ComputableClass S K Γ hk .ground q ↔ Least (scalarStep S K) (encodeAddress ⟨Γ,.ground,i⟩))

def ArrowAtEveryTypedArgument : Prop :=
  ∀ S K Γ σ τ (hk : DecisionSourceUniverse.Closed K) (q : Class S K (finiteC Γ) (.arrow σ τ)),
    ComputableClass S K Γ hk (.arrow σ τ) q ↔
      ∀ u : Class S K (finiteC Γ) σ, ComputableClass S K Γ hk σ u →
        ComputableClass S K Γ hk τ (appClass hk q u)

def ComputablePositiveDescendants : Prop :=
  ∀ S K Γ τ (hk : DecisionSourceUniverse.Closed K) (q r : Class S K (finiteC Γ) τ),
    RS S K (finiteC Γ) τ q r → ComputableClass S K Γ hk τ q → ComputableClass S K Γ hk τ r

def ComputableDirectDescendants : Prop :=
  ∀ S K Γ τ (hk : DecisionSourceUniverse.Closed K) (q r : Class S K (finiteC Γ) τ),
    ClassEdge q r → ComputableClass S K Γ hk τ q → ComputableClass S K Γ hk τ r

end LogicLineages.PersistentMarking.NumberedWindowExternalComputabilityTargets
