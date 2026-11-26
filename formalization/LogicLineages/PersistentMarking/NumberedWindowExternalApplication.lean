import LogicLineages.PersistentMarking.NumberedWindowApplicationDomainProof
import LogicLineages.PersistentMarking.NumberedWindowSimulationData

namespace LogicLineages.PersistentMarking.NumberedWindowExternalApplication
open NumberedWindowSyntax NumberedWindowPrimary NumberedWindowSimulationData

def appCarrier {S K C σ τ} (hk : DecisionSourceUniverse.Closed K)
    (q : WindowCarrier S K C (.arrow σ τ)) (u : WindowCarrier S K C σ) :
    WindowCarrier S K C τ :=
  ⟨.auxApp σ τ q.val u.val,
    NumberedWindowApplicationDomainProof.app S K C σ τ q.val u.val hk q.property u.property⟩

private def applyRepresentative {S K C σ τ} (hk : DecisionSourceUniverse.Closed K)
    (q : WindowCarrier S K C (.arrow σ τ)) : Class S K C σ → Class S K C τ :=
  Quot.lift (fun u => classOf (appCarrier hk q u))
    (fun _ _ h => Quot.sound (.appArgument q.property.1 h))

/-- The literal typed auxiliary application descends to the original
Primary quotient by its two application congruences. -/
def appClass {S K C σ τ} (hk : DecisionSourceUniverse.Closed K)
    (q : Class S K C (.arrow σ τ)) (u : Class S K C σ) : Class S K C τ :=
  Quot.lift (applyRepresentative hk) (fun q₁ q₂ h => by
    funext a
    refine Quot.inductionOn a ?_
    intro rep
    exact Quot.sound (.appFunction h rep.property.1)) q u

end LogicLineages.PersistentMarking.NumberedWindowExternalApplication
