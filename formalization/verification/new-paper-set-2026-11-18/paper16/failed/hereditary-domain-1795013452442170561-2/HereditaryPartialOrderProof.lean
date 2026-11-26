import LogicLineages.PersistentMarking.HereditaryOrderStepProof
namespace LogicLineages.PersistentMarking.HereditaryPartialOrderProof
open Spine FiniteDomainFoundation HereditaryOrderTargets

theorem bySize (E : HereditaryDomainCode.Environment) (n : Nat) :
    ∀ σ, typeSize σ = n → CarrierOrder E σ :=
  Nat.strongRecOn n (fun n ih σ hσ => HereditaryOrderStepProof.step E σ
    (fun ρ hρ => ih (typeSize ρ) (by omega) ρ rfl))

theorem partialOrder : HereditaryDomainTargets.PartialOrder := by
  intro E σ
  exact bySize E (typeSize σ) σ rfl

end LogicLineages.PersistentMarking.HereditaryPartialOrderProof
