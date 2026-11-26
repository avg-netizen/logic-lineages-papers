import LogicLineages.PersistentMarking.FiniteDomainSchemaTargets
import LogicLineages.PersistentMarking.FiniteEqualityProof
import LogicLineages.PersistentMarking.DecisionPortsProof
namespace LogicLineages.PersistentMarking.FiniteExtensionProof
open Spine NameBridge DecisionPorts FiniteDomainFoundation FiniteDomainSchema

theorem tail {a b : Option Ty} {Γ Δ : Context} (h : Extends (a::Γ) (b::Δ)) : Extends Γ Δ :=
  ⟨by simpa using h.1,fun i σ hi => h.2 (i+1) σ hi⟩

theorem test (Γ Δ : Context) : extendsBool Γ Δ = true ↔ Extends Γ Δ := by
  induction Γ generalizing Δ with
  | nil =>
    cases Δ with
    | nil => exact ⟨fun _ => ⟨rfl,fun i σ hi => by cases i <;> cases hi⟩,fun _ => rfl⟩
    | cons b Δ => exact ⟨(fun h => nomatch h),fun h => by have hh := h.1; simp at hh⟩
  | cons a Γ ih =>
    cases Δ with
    | nil => exact ⟨(fun h => nomatch h),fun h => by have hh := h.1; simp at hh⟩
    | cons b Δ =>
      cases a with
      | none =>
        change extendsBool Γ Δ = true ↔ _
        rw [ih]
        refine ⟨fun h => ⟨by simpa using h.1,?_⟩,tail⟩
        intro i σ hi
        cases i with
        | zero => cases hi
        | succ i => exact h.2 i σ hi
      | some σ =>
        cases b with
        | none =>
          exact ⟨(fun h => nomatch h),fun h => by have hh := h.2 0 σ rfl; cases hh⟩
        | some τ =>
          simp only [extendsBool,Bool.and_eq_true,decide_eq_true_eq,ih]
          constructor
          · rintro ⟨rfl,h⟩
            refine ⟨by simpa using h.1,?_⟩
            intro i ρ hi
            cases i with
            | zero => exact hi
            | succ i => exact h.2 i ρ hi
          · intro h
            have hh : σ=τ := Option.some.inj (Option.some.inj (h.2 0 σ rfl)).symm
            exact ⟨hh,tail h⟩

theorem enumeration : FiniteDomainSchemaTargets.ExtensionEnumeration := by
  intro K B Γ Δ
  simp only [extensions,List.mem_filter]
  rw [(FiniteEqualityProof.contexts (contexts K B)).1 Δ,DecisionPortsProof.enumeration,test]

theorem distinct : FiniteDomainSchemaTargets.ExtensionDistinct := by
  intro K B Γ
  exact ((FiniteEqualityProof.contexts (contexts K B)).2).filter _
end LogicLineages.PersistentMarking.FiniteExtensionProof
