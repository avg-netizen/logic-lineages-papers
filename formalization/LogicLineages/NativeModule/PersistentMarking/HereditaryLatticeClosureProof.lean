module

public import LogicLineages.NativeModule.PersistentMarking.HereditaryCombineEncodingProof
public import LogicLineages.NativeModule.PersistentMarking.HereditaryAggregateValidityProof
public import LogicLineages.NativeModule.PersistentMarking.HereditaryEncodeDecodeProof

@[expose] public section

namespace LogicLineages.PersistentMarking.HereditaryLatticeClosureProof
open Spine NameBridge DecisionPorts FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics HereditaryLatticeTargets

def operation (E : Environment) (σ : Ty) (Γ : Context) (meet : Bool) (cs : List Code) : Code :=
  if meet then (descriptor E σ).meet Γ cs else (descriptor E σ).join Γ cs

theorem operationCombine (E : Environment) (σ : Ty) (Γ : Context) (meet : Bool) (cs : List Code) :
    operation E σ Γ meet cs = combine E σ (canonicalLower E σ) Γ meet cs := by
  unfold operation
  rw [HereditaryConstructionProof.equation E σ]
  cases meet <;> rfl

theorem inputsValid (E : Environment) (σ : Ty) (Γ : Context) (cs : List Code)
    (hw : WellFormed E.types E.ports Γ) (hc : ∀ c, c ∈ cs → c ∈ (descriptor E σ).carriers Γ) :
    ∀ v, v ∈ cs.map (HereditaryDomainSemantics.decode E σ Γ) → Valid E σ Γ v := by
  intro v hv
  obtain ⟨c,hm,rfl⟩ := List.mem_map.mp hv
  exact HereditaryDecodedValidityProof.valid E σ Γ c hw (hc c hm)

theorem closure (E : Environment) (σ : Ty) (Γ : Context) (meet : Bool) (cs : List Code)
    (hw : WellFormed E.types E.ports Γ) (lower : LowerLattice E σ)
    (hc : ∀ c, c ∈ cs → c ∈ (descriptor E σ).carriers Γ) :
    operation E σ Γ meet cs ∈ (descriptor E σ).carriers Γ ∧
    ValueEq E σ Γ (HereditaryDomainSemantics.decode E σ Γ (operation E σ Γ meet cs))
      (aggregate E meet (cs.map (HereditaryDomainSemantics.decode E σ Γ))) := by
  rw [operationCombine,HereditaryCombineEncodingProof.encoding E σ Γ meet cs hw lower hc]
  exact HereditaryEncodeDecodeProof.encodeDecode E σ Γ _ hw
    (HereditaryAggregateValidityProof.valid E σ Γ meet _ hw lower (inputsValid E σ Γ cs hw hc))
end LogicLineages.PersistentMarking.HereditaryLatticeClosureProof
