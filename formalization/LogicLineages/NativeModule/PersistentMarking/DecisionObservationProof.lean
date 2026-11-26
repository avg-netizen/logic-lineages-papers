module

public import LogicLineages.NativeModule.PersistentMarking.DecisionOccurrenceProof
public import LogicLineages.NativeModule.PersistentMarking.DecisionAssignmentProof

@[expose] public section

namespace LogicLineages.PersistentMarking.DecisionObservationProof
open Spine NameBridge DecisionInventory DecisionPorts DecisionObservations

theorem enumeration (V : List Name) (B : Nat) (Γ : Context) (t : Expr) (σ : Ty) (r : Expr) :
    r ∈ observations V B Γ t σ ↔ Observation V B Γ t σ r := by
  constructor
  · intro h
    obtain ⟨⟨stack,q⟩,hocc,h⟩ := List.mem_flatMap.mp h
    split at h
    next ht =>
      obtain ⟨vs,hvs,hr⟩ := List.mem_map.mp h
      exact ⟨stack,q,vs,(DecisionOccurrenceProof.enumeration [] t stack q).mp hocc,
        (DecisionAssignmentProof.enumeration V Γ stack vs).mp hvs,ht.1,ht.2,hr.symm⟩
    next ht => cases h
  · rintro ⟨stack,q,vs,hocc,hvs,ht,hdepth,rfl⟩
    apply List.mem_flatMap.mpr
    refine ⟨(stack,q),(DecisionOccurrenceProof.enumeration [] t stack q).mpr hocc,?_⟩
    simp only [if_pos (show q.type = σ ∧ lambdaDepth q + used Γ ≤ B from ⟨ht,hdepth⟩)]
    exact List.mem_map.mpr ⟨vs,(DecisionAssignmentProof.enumeration V Γ stack vs).mpr hvs,rfl⟩

theorem paper (S : Signature) (V : List Name) (B : Nat) (Γ : Context) (t : Expr) (τ σ : Ty) (r : Expr)
    (ht : PaperTerm S t τ) (ho : Ordinary t) (hr : r ∈ observations V B Γ t σ) :
    PaperTerm S r σ ∧ Ordinary r ∧ lambdaDepth r + used Γ ≤ B := by
  obtain ⟨stack,q,vs,hocc,hvs,hτ,hdepth,rfl⟩ := (enumeration V B Γ t σ r).mp hr
  have hq := DecisionOccurrenceProof.typed [] t τ stack q ht.1 hocc
  have hqo := DecisionOccurrenceProof.ordinary [] t stack q ho hocc
  have hqv := DecisionOccurrenceProof.valid S [] t stack q ht.2 hocc
  have hty := DecisionAssignmentProof.openingTyped V Γ stack vs q q.type hvs hq
  obtain ⟨hd,hor,hvr⟩ := DecisionAssignmentProof.subFacts vs (DecisionAssignmentProof.freeValues V Γ stack vs hvs) 0 q
  refine ⟨⟨?_,hvr S hqv⟩,hor hqo,?_⟩
  · simpa only [hτ] using hty
  · simpa only [openOccurrence,hd] using hdepth
end LogicLineages.PersistentMarking.DecisionObservationProof
