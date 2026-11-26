module

public import LogicLineages.NativeModule.PersistentMarking.DecisionSourceSubstitutionProof
public import LogicLineages.NativeModule.PersistentMarking.DecisionObservationProof

@[expose] public section

namespace LogicLineages.PersistentMarking.DecisionObservedTypesProof
open Spine NameBridge TypeSupport DecisionInventory DecisionPorts DecisionObservations DecisionSourceUniverse DecisionSourceBasicProof

theorem portUniverse (K V H Γ σ q) (hk : Closed K) (hw : ∀ (i : Nat) (τ : Ty), Γ[i]? = some (some τ) → τ ∈ K)
    (hp : AtPort V Γ σ q) : Universe K V H Γ q := by
  obtain ⟨i,hi,rfl⟩ := hp
  refine ⟨fun τ hτ => hk σ (hw i σ hi) τ hτ,?_,?_⟩
  · intro f hf; cases hf
  · intro n hn
    have hn : n = (σ,portName V i) := by simpa only [freeOccurs,decide_eq_true_eq] using hn
    subst n; exact Or.inr ⟨i,hi,rfl⟩

theorem assignmentUniverse (K V H Γ stack vs) (hk : Closed K)
    (hw : ∀ (i : Nat) (τ : Ty), Γ[i]? = some (some τ) → τ ∈ K)
    (ha : Assignment V Γ stack vs) : ArgsUniverse K V H Γ vs := by
  induction ha with
  | nil => trivial
  | cons hq hqs ih => exact ⟨portUniverse K V H Γ _ _ hk hw hq,ih⟩

theorem observedTypes : DecisionSourceTargets.ObservedTypes := by
  intro S s t σ τ Γ υ r hs ht hos hot hw hobs
  let I := inventory s t
  have hk : Closed I.types := (initial s t σ τ hs.1 ht.1 hos hot).1
  have htu : Universe I.types I.names (heads t) Γ t := by
    refine ⟨?_,fun _ h => h,?_⟩
    · intro α hα
      exact List.mem_append_right _ ((DecisionInventoryProof.ordinaryExact EmptyContext t τ ht.1 hot α).mp hα)
    · intro n hn
      exact Or.inl (List.mem_append_right _ ((DecisionInventoryProof.freeExact t n).mpr hn))
  obtain ⟨stack,q,vs,hocc,hvs,hqtype,hdepth,rfl⟩ :=
    (DecisionObservationProof.enumeration I.names I.ports Γ t υ r).mp hobs
  have hqu := occurrence I.types I.names (heads t) Γ [] t stack q htu hocc
  have hqt := DecisionOccurrenceProof.typed [] t τ stack q ht.1 hocc
  have hvu := assignmentUniverse I.types I.names (heads t) Γ stack vs hk hw.2 hvs
  have hout := DecisionSourceSubstitutionProof.boundSubstitution I.types I.names (heads t) Γ stack vs q q.type
    hqt (DecisionAssignmentProof.typed I.names Γ stack vs hvs) hqu hvu
  exact hout.1
end LogicLineages.PersistentMarking.DecisionObservedTypesProof
