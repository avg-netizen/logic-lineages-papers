import LogicLineages.PersistentMarking.NumberedWindowRules

namespace LogicLineages.PersistentMarking.NumberedWindowPathLocality
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowRules

/-- Literal vertices of the actual full-tuple raw-path witness. A visit is
the path's first vertex or an actual visit in its original tail. No
alternative numeric result or intermediate guard is introduced. -/
inductive Visits (S : Spine.Signature) (K : List Ty) (C : Spine.BoundContext) (τ : Ty) :
    {q r : NTerm} → WindowPath S K C τ q r → NTerm → Prop where
  | start (path : WindowPath S K C τ q r) : Visits S K C τ path q
  | next (step : WindowStep S K C τ q r) (tail : WindowPath S K C τ r t) :
      Visits S K C τ tail u → Visits S K C τ (WindowPath.next step tail) u

def AllVisitsAdmitted {S K C τ q r} (path : WindowPath S K C τ q r) : Prop :=
  ∀ u, Visits S K C τ path u → InWindow S K C τ u

end LogicLineages.PersistentMarking.NumberedWindowPathLocality
