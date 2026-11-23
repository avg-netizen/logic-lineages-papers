module

public import LogicLineages.NativeModule.PersistentMarking.ProtectedSpineStrictInputProof
public import LogicLineages.NativeModule.PersistentMarking.ProtectedSpineLambdaFieldProof

@[expose] public section

namespace LogicLineages.PersistentMarking.ProtectedSpineStrictFieldLambdaStep
open Spine NameBridge DecisionInventory DecisionPorts DecisionObservations FiniteDomainSchema HereditaryDomainCode
open ProtectedSpineEnvironment ProtectedSpineLaws ProtectedSpineInterpreter ProtectedSpineInterpreterCore
open ProtectedSpineStrictTargets

/-- The original marking-fields contract, with only its structural input
pulled out as the recursor parameter. -/
def Point (S : Signature) (E : Environment) (H : List Head) (M : Code) (q : Expr) : Prop :=
  ∀ (Γ Δ : Context) (a : Assignments) (t : Expr),
    Covered E H q → InputValid E Γ a → StrictlessInputs E Γ a →
    WellFormed E.types E.ports Δ → Extends Γ Δ →
    t ∈ observations E.names E.ports Δ E.target q.type →
    (valueAt (evaluate S E H M q) Γ a).strict Δ t =
      match mark q with
      | none => false
      | some r => (valueAt (evaluate S E H M r) Γ a).weak Δ t

theorem lambdaWeak (S : Signature) (E : Environment) (H : List Head) (M : Code)
    (α : Ty) (body : Expr) (Γ : Context) (a : Assignments) :
    (valueAt (evaluate S E H M (.lam α body)) Γ a).weak =
      lambdaField E α (evaluate S E H M body) Γ a.free a.bound false := rfl

theorem lambdaStrict (S : Signature) (E : Environment) (H : List Head) (M : Code)
    (α : Ty) (body : Expr) (Γ : Context) (a : Assignments) :
    (valueAt (evaluate S E H M (.lam α body)) Γ a).strict =
      lambdaField E α (evaluate S E H M body) Γ a.free a.bound true := rfl

private theorem inactive (E : Environment) (α : Ty) (body : Evaluation) (Γ Δ : Context)
    (a : Assignments) (strict : Bool) (t : Expr)
    (h : ¬ ∃ target i, t = .lam α target ∧ openingSlot Δ = some i) :
    lambdaField E α body Γ a.free a.bound strict Δ t = false := by
  cases t with
  | free => rfl
  | bound => rfl
  | head => rfl
  | marked => rfl
  | lam β target =>
    by_cases hαβ : α = β
    · subst β
      cases hi : openingSlot Δ with
      | none => simp only [lambdaField,hi,if_true]
      | some i => exact (h ⟨target,i,rfl,hi⟩).elim
    · simp only [lambdaField,if_neg hαβ]

private theorem lambdaCovered (E : Environment) (H : List Head) (α : Ty) (body : Expr)
    (h : Covered E H (.lam α body)) : Covered E H body ∧ α ∈ E.types := by
  refine ⟨⟨fun τ ht => h.1 τ (List.mem_append_right _ ht),h.2⟩,h.1 α ?_⟩
  have hSelf : α ∈ TypeSupport.subtypes α := by cases α <;> simp only [TypeSupport.subtypes,List.mem_cons_self]
  exact List.mem_append_left _ (List.mem_append_right _ hSelf)

theorem step (S : Signature) (E : Environment) (H : List Head) (M : Code) (α : Ty) (body : Expr)
    (ih : Point S E H M body) : Point S E H M (.lam α body) := by
  intro Γ Δ a t hq ha hs hd he ht
  rw [lambdaStrict]
  by_cases hOp : ∃ target i, t = .lam α target ∧ openingSlot Δ = some i
  · obtain ⟨target,i,rfl,hi⟩ := hOp
    let Θ := openingContext Δ α i
    let x := portName E.names i
    let c := literalCode E Θ α x
    have hUnused := MarkedConstructorOpeningProof.slotUnused Δ i hi
    have hCov := lambdaCovered E H α body hq
    have hw := MarkedConstructorOpeningProof.openingWellFormed E.types E.ports Δ α i hd hCov.2 hUnused
    have hx := MarkedConstructorOpeningProof.openingExtends Δ α i hUnused
    have hExt := DecisionPortsProof.extensionTrans Γ Δ Θ he hx
    have hRetain := MarkedConstructorLiteralProof.literalRetained E Θ α x hw
    have hA := ProtectedSpineInputProof.restrictValid E Γ Θ a ha hw hExt
    have hS := ProtectedSpineStrictInputProof.weaken E Γ Θ a ha hs hw hExt
    have hObs := ProtectedSpineObservationProof.opened E Δ α body.type target i hUnused ht
    have hResult := ih Θ Θ ((a.restrict E Γ Θ).push α c) (openBody α x target)
      hCov.1 (ProtectedSpineInputProof.pushValid E Θ _ α c hA hRetain)
      (ProtectedSpineStrictInputProof.push E Θ _ α x hw hS)
      hw (DecisionPortsProof.extensionRefl Θ) hObs
    rw [ProtectedSpineLambdaFieldProof.fieldEq E α (evaluate S E H M body) Γ Δ a true target i hi]
    cases h : mark body with
    | none => simpa only [mark,h,Option.map_none,if_true] using hResult
    | some r =>
      simp only [mark,h,Option.map_some,lambdaWeak]
      rw [ProtectedSpineLambdaFieldProof.fieldEq E α (evaluate S E H M r) Γ Δ a false target i hi]
      simpa only [h,if_true,Bool.false_eq_true,if_false] using hResult
  · rw [inactive E α (evaluate S E H M body) Γ Δ a true t hOp]
    cases h : mark body with
    | none => simp only [mark,h,Option.map_none]
    | some r =>
      simp only [mark,h,Option.map_some,lambdaWeak]
      exact (inactive E α (evaluate S E H M r) Γ Δ a false t hOp).symm

end LogicLineages.PersistentMarking.ProtectedSpineStrictFieldLambdaStep
