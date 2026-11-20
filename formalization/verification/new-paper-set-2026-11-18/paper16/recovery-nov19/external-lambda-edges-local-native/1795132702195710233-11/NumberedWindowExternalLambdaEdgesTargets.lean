import LogicLineages.PersistentMarking.NumberedWindowExternalLambda
import LogicLineages.PersistentMarking.NumberedWindowExternalNeutralTargets

namespace LogicLineages.PersistentMarking.NumberedWindowExternalLambdaEdgesTargets
open Spine NumberedWindowSyntax NumberedWindowSimulationData NumberedWindowPrimary NumberedWindowExternalLambda
open NumberedWindowExternalApplication NumberedWindowExternalNeutralTargets NumberedWindowExternalSubstitutionTargets

def LambdaClassLiteral : Prop :=
  ∀ S K C σ τ (hk : DecisionSourceUniverse.Closed K) (hτ : Ty.arrow σ τ ∈ K)
    (v : WindowCarrier S K (C.push σ) τ),
    (lamCarrier hk hτ v).val = .lam σ v.val ∧ lamClass hk hτ (classOf v) = classOf (lamCarrier hk hτ v)

def PrimaryLambdaComponents : Prop :=
  ∀ S K C σ τ v out, Primary S K C (.arrow σ τ) (.lam σ v) out →
    ∃ w, out = .lam σ w ∧ Primary S K (C.push σ) τ v w

def LambdaEdges : Prop :=
  ∀ S K C σ τ (hk : DecisionSourceUniverse.Closed K) (hτ : Ty.arrow σ τ ∈ K)
    (v : Class S K (C.push σ) τ) (out : Class S K C (.arrow σ τ)),
    ClassEdge (lamClass hk hτ v) out →
      ClassBottom out ∨ ∃ w, ClassEdge v w ∧ out = lamClass hk hτ w

/-- The result-bottom and the application with a bottom function are distinct alternatives.
The beta branch uses current representatives, their original body instance and the fixed argument class. -/
def LambdaApplicationEdges : Prop :=
  ∀ S K C σ τ (hk : DecisionSourceUniverse.Closed K) (hτ : Ty.arrow σ τ ∈ K)
    (v : Class S K (C.push σ) τ) (u : Class S K C σ) (out : Class S K C τ),
    ClassEdge (appClass hk (lamClass hk hτ v) u) out →
      ClassBottom out ∨
      (∃ b : Class S K C (.arrow σ τ), ClassBottom b ∧ out = appClass hk b u) ∨
      (∃ w, ClassEdge v w ∧ out = appClass hk (lamClass hk hτ w) u) ∨
      (∃ (body : WindowCarrier S K (C.push σ) τ) (arg : WindowCarrier S K C σ),
        classOf body = v ∧ classOf arg = u ∧ out = classOf (bodyInstance hk body arg))

end LogicLineages.PersistentMarking.NumberedWindowExternalLambdaEdgesTargets
