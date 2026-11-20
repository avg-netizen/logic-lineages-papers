import LogicLineages.PersistentMarking.NumberedWindowExternalApplication

namespace LogicLineages.PersistentMarking.NumberedWindowExternalNeutralTargets
open NumberedWindowSyntax NumberedWindowPrimary NumberedWindowSimulationData
open NumberedWindowExternalApplication

def NonLambda (q : NTerm) : Prop := ∀ σ body, q ≠ .lam σ body

def ClassNonLambda {S K C τ} (x : Class S K C τ) : Prop :=
  ∀ q : WindowCarrier S K C τ, classOf q = x → NonLambda q.val

def ClassBottom {S K C τ} (x : Class S K C τ) : Prop :=
  ∃ q : WindowCarrier S K C τ, q.val = .bottom τ ∧ classOf q = x

def PrimaryPreservesNonLambda : Prop :=
  ∀ S K C τ q r, Primary S K C τ q r → (NonLambda q ↔ NonLambda r)

def ExactNonLambdaRepresentatives : Prop :=
  ∀ S K C τ (q : WindowCarrier S K C τ), ClassNonLambda (classOf q) ↔ NonLambda q.val

def PrimaryAuxApplicationComponents : Prop :=
  ∀ S K C σ τ q u out,
    Primary S K C τ (.auxApp σ τ q u) out →
    ∃ r v, out = .auxApp σ τ r v ∧ Primary S K C (.arrow σ τ) q r ∧ Primary S K C σ u v

def NonLambdaApplicationClass : Prop :=
  ∀ S K C σ τ (hk : DecisionSourceUniverse.Closed K)
    (q : Class S K C (.arrow σ τ)) (u : Class S K C σ),
      ClassNonLambda (appClass hk q u)

/-- Every actual one-step reduct of a neutral application is bottom
or comes from a strict function-side edge at the same argument class. -/
def NeutralApplicationEdges : Prop :=
  ∀ S K C σ τ (hk : DecisionSourceUniverse.Closed K)
    (q : Class S K C (.arrow σ τ)) (u : Class S K C σ) (out : Class S K C τ),
    ClassNonLambda q → ClassEdge (appClass hk q u) out →
    ClassBottom out ∨ ∃ next, ClassEdge q next ∧ out = appClass hk next u

end LogicLineages.PersistentMarking.NumberedWindowExternalNeutralTargets
