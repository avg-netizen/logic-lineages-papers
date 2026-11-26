module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowExternalApplication
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowExternalIDOperators

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowExternalApplicationTargets
open Spine NumberedWindowSyntax NumberedWindowSimulationData NumberedWindowExternalApplication
open NumberedWindowExternalIDOperators NumberedWindowArithmeticClassAddress
open NumberedWindowArithmeticLeastClass NumberedWindowPathWitnessTargets

def QuotientApplicationLiteral : Prop :=
  ∀ S K C σ τ (hk : DecisionSourceUniverse.Closed K)
    (q : WindowCarrier S K C (.arrow σ τ)) (u : WindowCarrier S K C σ),
    (appCarrier hk q u).val = NTerm.auxApp σ τ q.val u.val ∧
      appClass hk (classOf q) (classOf u) = classOf (appCarrier hk q u)

def QuotientAppPreservesPositive : Prop :=
  ∀ S K C σ τ (hk : DecisionSourceUniverse.Closed K)
    (q r : Class S K C (.arrow σ τ)) (u : Class S K C σ),
    RS S K C (.arrow σ τ) q r → RS S K C τ (appClass hk q u) (appClass hk r u)

/-- External I at any actual canonical address of a typed quotient class. -/
def ScalarClassAccessibility : Prop :=
  ∀ S K Γ τ, DecisionSourceUniverse.Closed K →
  ∀ (q : Class S K (finiteC Γ) τ) i, ActualCodeAt S K Γ τ i q →
    (Least (scalarStep S K) (encodeAddress ⟨Γ,τ,i⟩) ↔
      Acc (fun r q => RS S K (finiteC Γ) τ q r) q)

/-- The application and function are measured in one original finite context,
at their respective canonical addresses and literal result types. -/
def ExternalIApplicationPullback : Prop :=
  ∀ S K Γ σ τ (hk : DecisionSourceUniverse.Closed K)
    (q : Class S K (finiteC Γ) (.arrow σ τ)) (u : Class S K (finiteC Γ) σ) i j,
    ActualCodeAt S K Γ (.arrow σ τ) i q →
    ActualCodeAt S K Γ τ j (appClass hk q u) →
    Least (scalarStep S K) (encodeAddress ⟨Γ,τ,j⟩) →
    Least (scalarStep S K) (encodeAddress ⟨Γ,.arrow σ τ,i⟩)

end LogicLineages.PersistentMarking.NumberedWindowExternalApplicationTargets
