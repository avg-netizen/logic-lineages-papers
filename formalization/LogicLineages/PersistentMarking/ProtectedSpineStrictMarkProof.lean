import LogicLineages.PersistentMarking.ProtectedSpineStrictInputProof
import LogicLineages.PersistentMarking.ProtectedSpineLambdaFieldProof
import LogicLineages.PersistentMarking.ProtectedSpineCoverageProof

namespace LogicLineages.PersistentMarking.ProtectedSpineStrictMarkProof
open Spine NameBridge DecisionPorts DecisionObservations FiniteDomainSchema HereditaryDomainCode
open ProtectedSpineEnvironment ProtectedSpineLaws ProtectedSpineInterpreter ProtectedSpineInterpreterCore
open ProtectedSpineStrictTargets

theorem lambdaWeak (S : Signature) (E : Environment) (H : List Head) (M : Code)
    (α : Ty) (body : Expr) (Γ : Context) (a : Assignments) :
    (valueAt (evaluate S E H M (.lam α body)) Γ a).weak =
      lambdaField E α (evaluate S E H M body) Γ a.free a.bound false := rfl

theorem lambdaStrict (S : Signature) (E : Environment) (H : List Head) (M : Code)
    (α : Ty) (body : Expr) (Γ : Context) (a : Assignments) :
    (valueAt (evaluate S E H M (.lam α body)) Γ a).strict =
      lambdaField E α (evaluate S E H M body) Γ a.free a.bound true := rfl

theorem marking (S : Signature) (E : Environment) (H : List Head) (M : Code)
    (Γ Δ : Context) (a : Assignments) (q t : Expr)
    (hq : Covered E H q) (ha : InputValid E Γ a) (hs : StrictlessInputs E Γ a)
    (hd : WellFormed E.types E.ports Δ) (he : Extends Γ Δ)
    (ht : t ∈ observations E.names E.ports Δ E.target q.type) :
    (valueAt (evaluate S E H M q) Γ a).strict Δ t =
      match mark q with
      | none => false
      | some r => (valueAt (evaluate S E H M r) Γ a).weak Δ t := by
  cases q with
  | free σ x => exact (hs Δ hd he σ t ht).1 x
  | bound σ i => exact (hs Δ hd he σ t ht).2 i
  | head f bs => rfl
  | marked f τ bs es => rfl
  | lam α body =>
    rw [lambdaStrict]
    cases t with
    | free τ x => cases h : mark body <;> simp [mark,h,lambdaWeak,lambdaField]
    | bound τ i => cases h : mark body <;> simp [mark,h,lambdaWeak,lambdaField]
    | head f ts => cases h : mark body <;> simp [mark,h,lambdaWeak,lambdaField]
    | marked f τ bs es => cases h : mark body <;> simp [mark,h,lambdaWeak,lambdaField]
    | lam β target =>
      by_cases hαβ : α = β
      · subst β
        cases hi : openingSlot Δ with
        | none => cases h : mark body <;> simp [mark,h,lambdaWeak,lambdaField,hi]
        | some i =>
          let Θ := openingContext Δ α i
          let x := portName E.names i
          let c := literalCode E Θ α x
          have hUnused := MarkedConstructorOpeningProof.slotUnused Δ i hi
          have hType := ProtectedSpineCoverageProof.lambdaType E H α body hq
          have hw := MarkedConstructorOpeningProof.openingWellFormed E.types E.ports Δ α i hd hType hUnused
          have hx := MarkedConstructorOpeningProof.openingExtends Δ α i hUnused
          have hExt := DecisionPortsProof.extensionTrans Γ Δ Θ he hx
          have hRetain := MarkedConstructorLiteralProof.literalRetained E Θ α x hw
          have hA := ProtectedSpineInputProof.restrictValid E Γ Θ a ha hw hExt
          have hS := ProtectedSpineStrictInputProof.weaken E Γ Θ a ha hs hw hExt
          have hObs := ProtectedSpineObservationProof.opened E Δ α body.type target i hUnused ht
          have hResult := marking S E H M Θ Θ ((a.restrict E Γ Θ).push α c) body (openBody α x target)
            (ProtectedSpineCoverageProof.lambdaBody E H α body hq)
            (ProtectedSpineInputProof.pushValid E Θ _ α c hA hRetain)
            (ProtectedSpineStrictInputProof.push E Θ _ α x hw hS)
            hw (DecisionPortsProof.extensionRefl Θ) hObs
          rw [ProtectedSpineLambdaFieldProof.fieldEq E α (evaluate S E H M body) Γ Δ a true target i hi]
          cases h : mark body with
          | none =>
            simpa only [mark,h,Option.map_none,if_true] using hResult
          | some r =>
            simp only [mark,h,Option.map_some,lambdaWeak]
            rw [ProtectedSpineLambdaFieldProof.fieldEq E α (evaluate S E H M r) Γ Δ a false target i hi]
            simpa only [h,if_true,Bool.false_eq_true,if_false] using hResult
      · cases h : mark body <;> simp [mark,h,lambdaWeak,lambdaField,hαβ]
termination_by sizeOf q

theorem exact_MarkingFields : MarkingFields := marking
#print axioms exact_MarkingFields
end LogicLineages.PersistentMarking.ProtectedSpineStrictMarkProof
