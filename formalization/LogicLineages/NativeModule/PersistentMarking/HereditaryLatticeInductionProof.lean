module

public import LogicLineages.NativeModule.PersistentMarking.HereditaryLatticeStepProof

@[expose] public section

namespace LogicLineages.PersistentMarking.HereditaryLatticeInductionProof
open Spine NameBridge DecisionPorts FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics HereditaryLatticeTargets

theorem bySize (E : Environment) (n : Nat) : ∀ σ, typeSize σ = n → LatticeAt E σ :=
  Nat.strongRecOn n (fun n ih σ hσ => HereditaryLatticeStepProof.step E σ
    (fun ρ hρ => ih (typeSize ρ) (by omega) ρ rfl))

theorem lattice (E : Environment) (σ : Ty) : LatticeAt E σ := bySize E (typeSize σ) σ rfl

theorem join : HereditaryDomainTargets.Join := by
  intro E σ
  exact (lattice E σ).1

theorem meet : HereditaryDomainTargets.Meet := by
  intro E σ
  exact (lattice E σ).2.1

theorem restriction : HereditaryDomainTargets.RestrictionJoinsMeets := by
  intro E σ
  exact (lattice E σ).2.2
end LogicLineages.PersistentMarking.HereditaryLatticeInductionProof
