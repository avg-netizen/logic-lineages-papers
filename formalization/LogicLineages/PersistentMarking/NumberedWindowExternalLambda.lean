import LogicLineages.PersistentMarking.NumberedWindowExternalSubstitutionTargets
import LogicLineages.PersistentMarking.NumberedWindowExternalApplication
import LogicLineages.PersistentMarking.NumberedWindowPreservationGuardProof

namespace LogicLineages.PersistentMarking.NumberedWindowExternalLambda
open Spine NumberedWindowSyntax NumberedWindowSimulationData NumberedWindowPrimary

def lamCarrier {S K C σ τ} (hk : DecisionSourceUniverse.Closed K) (hτ : Ty.arrow σ τ ∈ K)
    (v : WindowCarrier S K (C.push σ) τ) : WindowCarrier S K C (.arrow σ τ) :=
  ⟨.lam σ v.val, NumberedWindowPreservationGuardProof.lam (hk _ hτ) v.property⟩

def lamClass {S K C σ τ} (hk : DecisionSourceUniverse.Closed K) (hτ : Ty.arrow σ τ ∈ K) :
    Class S K (C.push σ) τ → Class S K C (.arrow σ τ) :=
  Quot.lift (fun v => classOf (lamCarrier hk hτ v)) (fun _ _ h => Quot.sound (.lam h))

end LogicLineages.PersistentMarking.NumberedWindowExternalLambda
