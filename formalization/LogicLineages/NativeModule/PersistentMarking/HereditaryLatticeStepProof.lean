module

public import LogicLineages.NativeModule.PersistentMarking.HereditaryLatticeBoundsProof
public import LogicLineages.NativeModule.PersistentMarking.HereditaryAggregateCongruenceProof

@[expose] public section

namespace LogicLineages.PersistentMarking.HereditaryLatticeStepProof
open Spine NameBridge DecisionPorts FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics HereditaryLatticeTargets HereditaryLatticeClosureProof

theorem restrictionOperation (E : Environment) (σ : Ty) (lower : LowerLattice E σ)
    (Γ Θ : Context) (meet : Bool) (cs : List Code) (hw : WellFormed E.types E.ports Γ)
    (ht : WellFormed E.types E.ports Θ) (he : Extends Γ Θ)
    (hc : ∀ c, c ∈ cs → c ∈ (descriptor E σ).carriers Γ) :
    (descriptor E σ).restrict Γ Θ (operation E σ Γ meet cs) =
      operation E σ Θ meet (cs.map ((descriptor E σ).restrict Γ Θ)) := by
  have hsource := closure E σ Γ meet cs hw lower hc
  have hrest := HereditaryRestrictionProof.restriction E σ Γ Θ hw ht he _ hsource.1
  have hcs : ∀ c, c ∈ cs.map ((descriptor E σ).restrict Γ Θ) → c ∈ (descriptor E σ).carriers Θ := by
    intro c hm; obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hm
    exact (HereditaryRestrictionProof.restriction E σ Γ Θ hw ht he x (hc x hx)).1
  have htarget := closure E σ Θ meet _ ht lower hcs
  apply HereditaryEncodingCongruenceProof.injective E σ Θ _ _ hrest.1 htarget.1
  exact HereditaryValueEqualityProof.trans hrest.2
    (HereditaryValueEqualityProof.trans (HereditaryValueEqualityProof.weaken he hsource.2)
      (HereditaryValueEqualityProof.trans (HereditaryAggregateCongruenceProof.restriction E σ Γ Θ meet cs hw ht he hc)
        (HereditaryValueEqualityProof.symm htarget.2)))

theorem step : LatticeStep := by
  intro E σ lower
  have hbounds := HereditaryLatticeBoundsProof.bounds E σ lower
  refine ⟨hbounds.1,hbounds.2,?_⟩
  intro Γ Θ cs hw ht he hc
  exact ⟨restrictionOperation E σ lower Γ Θ false cs hw ht he hc,
    restrictionOperation E σ lower Γ Θ true cs hw ht he hc⟩
end LogicLineages.PersistentMarking.HereditaryLatticeStepProof
