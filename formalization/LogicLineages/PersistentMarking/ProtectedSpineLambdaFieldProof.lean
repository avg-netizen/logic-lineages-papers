import LogicLineages.PersistentMarking.ProtectedSpineInputProof
import LogicLineages.PersistentMarking.ProtectedSpineObservationProof

namespace LogicLineages.PersistentMarking.ProtectedSpineLambdaFieldProof
open Spine NameBridge DecisionPorts DecisionObservations HereditaryDomainCode HereditaryDomainSemantics
open ProtectedSpineEnvironment ProtectedSpineInterpreterCore ProtectedSpineLaws

theorem fieldEq (E : Environment) (σ : Ty) (body : Evaluation) (Γ Δ : Context)
    (a : Assignments) (strict : Bool) (target : Expr) (i : Nat) (hi : openingSlot Δ = some i) :
    lambdaField E σ body Γ a.free a.bound strict Δ (.lam σ target) =
      let Θ := openingContext Δ σ i
      let x := portName E.names i
      let v := valueAt body Θ ((a.restrict E Γ Θ).push σ (literalCode E Θ σ x))
      if strict then v.strict Θ (openBody σ x target) else v.weak Θ (openBody σ x target) := by
  simp [lambdaField,hi,valueAt,Assignments.push,Assignments.restrict]

theorem natural (E : Environment) (σ : Ty) (body : Evaluation) (Γ Δ Θ : Context)
    (a : Assignments) (ha : InputValid E Γ a) (hd : WellFormed E.types E.ports Δ)
    (ht : WellFormed E.types E.ports Θ) (he : Extends Γ Δ) (hf : Extends Δ Θ)
    (hσ : σ ∈ E.types) (strict : Bool) (t : Expr) :
    lambdaField E σ body Γ a.free a.bound strict Θ t =
      lambdaField E σ body Δ (a.restrict E Γ Δ).free (a.restrict E Γ Δ).bound strict Θ t := by
  cases t with
  | lam ρ target =>
    by_cases h : σ = ρ
    · subst ρ
      cases hs : openingSlot Θ with
      | none => simp [lambdaField,hs]
      | some i =>
        let Ξ := openingContext Θ σ i
        have hi := MarkedConstructorOpeningProof.slotUnused Θ i hs
        have hw := MarkedConstructorOpeningProof.openingWellFormed E.types E.ports Θ σ i ht hσ hi
        have hx := MarkedConstructorOpeningProof.openingExtends Θ σ i hi
        have he' := DecisionPortsProof.extensionTrans Δ Θ Ξ hf hx
        have hc := ProtectedSpineInputProof.restrictCompose E Γ Δ Ξ a ha hd hw he he'
        rw [fieldEq E σ body Γ Θ a strict target i hs,
          fieldEq E σ body Δ Θ (a.restrict E Γ Δ) strict target i hs]
        dsimp only
        rw [show (a.restrict E Γ Δ).restrict E Δ (openingContext Θ σ i) =
          a.restrict E Γ (openingContext Θ σ i) from hc]
    · simp [lambdaField,h]
  | free ρ x => rfl
  | bound ρ i => rfl
  | head f ts => rfl
  | marked f ρ bs es => rfl

theorem monotone (E : Environment) (σ ρ : Ty) (body : Evaluation) (hl : EvaluationLaws E ρ body)
    (Γ Δ : Context) (a b : Assignments) (ha : InputValid E Γ a) (hb : InputValid E Γ b)
    (hle : InputLE E Γ a b) (hd : WellFormed E.types E.ports Δ) (he : Extends Γ Δ)
    (hσ : σ ∈ E.types) (strict : Bool) (t : Expr)
    (ht : t ∈ observations E.names E.ports Δ E.target (.arrow σ ρ))
    (hbit : lambdaField E σ body Γ a.free a.bound strict Δ t = true) :
    lambdaField E σ body Γ b.free b.bound strict Δ t = true := by
  cases t with
  | lam υ target =>
    by_cases h : σ = υ
    · subst υ
      cases hs : openingSlot Δ with
      | none => simp [lambdaField,hs] at hbit
      | some i =>
        let Θ := openingContext Δ σ i
        let x := portName E.names i
        let v := literalCode E Θ σ x
        have hi := MarkedConstructorOpeningProof.slotUnused Δ i hs
        have hw := MarkedConstructorOpeningProof.openingWellFormed E.types E.ports Δ σ i hd hσ hi
        have hx := MarkedConstructorOpeningProof.openingExtends Δ σ i hi
        have he' := DecisionPortsProof.extensionTrans Γ Δ Θ he hx
        have hv := MarkedConstructorLiteralProof.literalRetained E Θ σ x hw
        have ha' := ProtectedSpineInputProof.pushValid E Θ _ σ v
          (ProtectedSpineInputProof.restrictValid E Γ Θ a ha hw he') hv
        have hb' := ProtectedSpineInputProof.pushValid E Θ _ σ v
          (ProtectedSpineInputProof.restrictValid E Γ Θ b hb hw he') hv
        have hle' := ProtectedSpineInputProof.pushOrder E Θ
          (a.restrict E Γ Θ) (b.restrict E Γ Θ) σ v v hw
          (ProtectedSpineInputProof.restrictOrder E Γ Θ a b ha hb hle hw he')
          ((HereditaryPartialOrderProof.partialOrder E σ Θ hw).1 v hv)
        have hobs := ProtectedSpineObservationProof.opened E Δ σ ρ target i hi ht
        have hfields := (hl.monotone Θ _ _ ha' hb' hle' Θ hw
          (DecisionPortsProof.extensionRefl Θ)).2.1 (openBody σ x target) hobs
        rw [fieldEq E σ body Γ Δ a strict target i hs] at hbit
        rw [fieldEq E σ body Γ Δ b strict target i hs]
        cases strict
        · exact hfields.1 hbit
        · exact hfields.2 hbit
    · simp [lambdaField,h] at hbit
  | free υ x => cases hbit
  | bound υ i => cases hbit
  | head f ts => cases hbit
  | marked f υ bs es => cases hbit

end LogicLineages.PersistentMarking.ProtectedSpineLambdaFieldProof
