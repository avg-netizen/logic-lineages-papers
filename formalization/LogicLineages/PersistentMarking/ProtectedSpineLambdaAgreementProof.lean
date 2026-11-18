import LogicLineages.PersistentMarking.ProtectedSpineAgreementTargets
import LogicLineages.PersistentMarking.ProtectedSpineLambdaProof

namespace LogicLineages.PersistentMarking.ProtectedSpineLambdaAgreementProof
open Spine NameBridge DecisionPorts FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics
open ProtectedSpineEnvironment ProtectedSpineLaws ProtectedSpineAgreementTargets
open ProtectedSpineInterpreterCore ProtectedSpineLambdaCallProof

theorem callEq (E : Environment) (σ ρ : Ty) (v w : Evaluation)
    (R R' : FrameRelation) (P P' : Nat → Nat → Prop) (hChild : Agreement E ρ v w R' P')
    (push : ∀ Γ a b c, InputValid E Γ a → InputValid E Γ b → R Γ a b →
      c ∈ (descriptor E σ).carriers Γ → R' Γ (a.push σ c) (b.push σ c))
    (pushProtection : ∀ k l, P k l → P' (k+1) (l+1))
    (Γ : Context) (a b : Assignments) (k l : Nat) (ds : List Ty) (τ : Ty) (xs : List Code)
    (ha : InputValid E Γ a) (hb : InputValid E Γ b) (hr : R Γ a b) (hc : P k l)
    (hpre : (ds,τ) ∈ fullPrefixes (.arrow σ ρ)) (hx : TupleValues E Γ ds xs) :
    nonemptyAt E (lambdaEvaluation E σ ρ v) Γ a k ds τ xs =
      nonemptyAt E (lambdaEvaluation E σ ρ w) Γ b l ds τ xs := by
  cases prefixCase σ ρ ds τ hpre with
  | last =>
    cases xs with
    | nil => cases hx.1
    | cons x xs =>
      have ht := (HereditaryTupleProof.tupleCons E Γ σ [] x xs).mp hx
      cases xs with
      | cons y ys => cases ht.2.1
      | nil =>
        rw [last,last]
        exact HereditaryEncodingCongruenceProof.congruence E ρ Γ _ _
          (hChild.value Γ _ _ (ProtectedSpineInputProof.pushValid E Γ a σ x ha ht.1)
            (ProtectedSpineInputProof.pushValid E Γ b σ x hb ht.1) (push Γ a b x ha hb hr ht.1))
  | @more d ds τ hp =>
    cases xs with
    | nil => cases hx.1
    | cons x xs =>
      have ht := (HereditaryTupleProof.tupleCons E Γ σ (d::ds) x xs).mp hx
      cases xs with
      | nil => cases ht.2.1
      | cons y ys =>
        rw [more,more]
        exact hChild.call Γ _ _ (k+1) (l+1) _ τ _
          (ProtectedSpineInputProof.pushValid E Γ a σ x ha ht.1)
          (ProtectedSpineInputProof.pushValid E Γ b σ x hb ht.1)
          (push Γ a b x ha hb hr ht.1) (pushProtection k l hc) hp ht.2

theorem field (E : Environment) (σ ρ : Ty) (v w : Evaluation)
    (R R' : FrameRelation) (P' : Nat → Nat → Prop) (hChild : Agreement E ρ v w R' P')
    (weaken : ∀ Γ Δ a b, InputValid E Γ a → InputValid E Γ b → R Γ a b →
      WellFormed E.types E.ports Δ → Extends Γ Δ → R Δ (a.restrict E Γ Δ) (b.restrict E Γ Δ))
    (push : ∀ Γ a b c, InputValid E Γ a → InputValid E Γ b → R Γ a b →
      c ∈ (descriptor E σ).carriers Γ → R' Γ (a.push σ c) (b.push σ c))
    (hσ : σ ∈ E.types) (Γ Δ : Context) (a b : Assignments)
    (ha : InputValid E Γ a) (hb : InputValid E Γ b) (hr : R Γ a b)
    (hd : WellFormed E.types E.ports Δ) (he : Extends Γ Δ)
    (strict : Bool) (t : Expr)
    (ht : t ∈ DecisionObservations.observations E.names E.ports Δ E.target (.arrow σ ρ)) :
    lambdaField E σ v Γ a.free a.bound strict Δ t = lambdaField E σ w Γ b.free b.bound strict Δ t := by
  cases t with
  | lam υ target =>
    by_cases h : σ = υ
    · subst υ
      cases hi : openingSlot Δ with
      | none => simp [lambdaField,hi]
      | some i =>
        let Θ := openingContext Δ σ i
        let x := portName E.names i
        let c := literalCode E Θ σ x
        have hnone := MarkedConstructorOpeningProof.slotUnused Δ i hi
        have hw := MarkedConstructorOpeningProof.openingWellFormed E.types E.ports Δ σ i hd hσ hnone
        have he' := DecisionPortsProof.extensionTrans Γ Δ Θ he
          (MarkedConstructorOpeningProof.openingExtends Δ σ i hnone)
        have hc := MarkedConstructorLiteralProof.literalRetained E Θ σ x hw
        have ha' := ProtectedSpineInputProof.restrictValid E Γ Θ a ha hw he'
        have hb' := ProtectedSpineInputProof.restrictValid E Γ Θ b hb hw he'
        have hr' := push Θ _ _ c ha' hb' (weaken Γ Θ a b ha hb hr hw he') hc
        have hv := hChild.value Θ _ _
          (ProtectedSpineInputProof.pushValid E Θ _ σ c ha' hc)
          (ProtectedSpineInputProof.pushValid E Θ _ σ c hb' hc) hr'
        have hobs := ProtectedSpineObservationProof.opened E Δ σ ρ target i hnone ht
        have hfield := (hv Θ hw (DecisionPortsProof.extensionRefl Θ)).2.1 (openBody σ x target) hobs
        rw [ProtectedSpineLambdaFieldProof.fieldEq E σ v Γ Δ a strict target i hi,
          ProtectedSpineLambdaFieldProof.fieldEq E σ w Γ Δ b strict target i hi]
        cases strict
        · exact hfield.1
        · exact hfield.2
    · simp [lambdaField,h]
  | free υ x => rfl
  | bound υ i => rfl
  | head f ts => rfl
  | marked f υ bs es => rfl

theorem lambda (E : Environment) (σ ρ : Ty) (v w : Evaluation)
    (R R' : FrameRelation) (P P' : Nat → Nat → Prop) (hChild : Agreement E ρ v w R' P')
    (weaken : ∀ Γ Δ a b, InputValid E Γ a → InputValid E Γ b → R Γ a b →
      WellFormed E.types E.ports Δ → Extends Γ Δ → R Δ (a.restrict E Γ Δ) (b.restrict E Γ Δ))
    (push : ∀ Γ a b c, InputValid E Γ a → InputValid E Γ b → R Γ a b →
      c ∈ (descriptor E σ).carriers Γ → R' Γ (a.push σ c) (b.push σ c))
    (pushProtection : ∀ k l, P k l → P' (k+1) (l+1)) (initial : P 0 0)
    (hσ : σ ∈ E.types) :
    Agreement E (.arrow σ ρ) (lambdaEvaluation E σ ρ v) (lambdaEvaluation E σ ρ w) R P := by
  refine ⟨?_,callEq E σ ρ v w R R' P P' hChild push pushProtection⟩
  intro Γ a b ha hb hr Δ hd he
  refine ⟨rfl,?_,?_⟩
  · intro t ht
    exact ⟨field E σ ρ v w R R' P' hChild weaken push hσ Γ Δ a b ha hb hr hd he false t ht,
      field E σ ρ v w R R' P' hChild weaken push hσ Γ Δ a b ha hb hr hd he true t ht⟩
  · intro ds τ hp xs hx
    rw [ProtectedSpineLambdaProof.applicationEq,ProtectedSpineLambdaProof.applicationEq]
    exact callEq E σ ρ v w R R' P P' hChild push pushProtection Δ _ _ 0 0 ds τ xs
      (ProtectedSpineInputProof.restrictValid E Γ Δ a ha hd he)
      (ProtectedSpineInputProof.restrictValid E Γ Δ b hb hd he)
      (weaken Γ Δ a b ha hb hr hd he) initial hp hx

end LogicLineages.PersistentMarking.ProtectedSpineLambdaAgreementProof
