import LogicLineages.PersistentMarking.NumberedWindowExternalInstance
import LogicLineages.PersistentMarking.NumberedWindowExternalLambdaEdgesTargets
import LogicLineages.PersistentMarking.NumberedWindowExternalComputability

namespace LogicLineages.PersistentMarking.NumberedWindowExternalLambdaComputabilityTargets
open Spine NumberedWindowSyntax NumberedWindowSimulationData NumberedWindowExternalInstance
open NumberedWindowExternalSubstitutionTargets NumberedWindowExternalLambda NumberedWindowExternalApplication
open NumberedWindowExternalNeutralTargets NumberedWindowArithmeticLeastClass NumberedWindowExternalComputability

def InstanceClassLiteral : Prop :=
  ∀ S K (C : BoundContext) σ τ (hk : DecisionSourceUniverse.Closed K)
    (v : WindowCarrier S K (C.push σ) τ) (u : WindowCarrier S K C σ),
    instanceClass hk (classOf v) (classOf u) = classOf (bodyInstance hk v u)

def AppliedLambdaReducts : Prop :=
  ∀ S K (C : BoundContext) σ τ (hk : DecisionSourceUniverse.Closed K) (hτ : Ty.arrow σ τ ∈ K)
    (v : Class S K (C.push σ) τ) (u : Class S K C σ) (out : Class S K C τ),
    ClassEdge (appClass hk (lamClass hk hτ v) u) out →
      ClassBottom out ∨
      (∃ b : Class S K C (.arrow σ τ), ClassBottom b ∧ out = appClass hk b u) ∨
      (∃ w, ClassEdge v w ∧ out = appClass hk (lamClass hk hτ w) u) ∨
      out = instanceClass hk v u

def ComputableLambda : Prop :=
  ∀ S K Γ σ τ (hk : DecisionSourceUniverse.Closed K) (hτ : Ty.arrow σ τ ∈ K)
    (v : Class S K ((finiteC Γ).push σ) τ),
    (∀ u : Class S K (finiteC Γ) σ, ComputableClass S K Γ hk σ u →
      ComputableClass S K Γ hk τ (instanceClass hk v u)) →
    ComputableClass S K Γ hk (.arrow σ τ) (lamClass hk hτ v)

end LogicLineages.PersistentMarking.NumberedWindowExternalLambdaComputabilityTargets
