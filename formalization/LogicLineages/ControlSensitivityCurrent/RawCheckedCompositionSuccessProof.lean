module
public import LogicLineages.ControlSensitivityCurrent.RawCheckedCompositionTypedProof
public import LogicLineages.ControlSensitivityCurrent.RawSourceDAGRawValidatorLookupProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.RawSourceDAG.CheckedComposition
open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source GroundEquivalence

theorem application_success (t : Nat) (cf ca co : Code) (h : application t cf ca = some co) :
    ∃ (Γ : List Ty) (σ τ : Ty) (f : Input Γ (.arrow σ τ)) (a : Input Γ σ),
      SyntaxCode.typeCode τ=t ∧ encode ⟨Γ,.arrow σ τ,f⟩=cf ∧ encode ⟨Γ,σ,a⟩=ca ∧
      encode ⟨Γ,τ,ScopedDAG.application f a⟩=co ∧
      decode co=some ⟨Γ,τ,ScopedDAG.application f a⟩ := by
  have hg : applicationGuard t cf ca = true := by
    unfold application at h
    split at h
    next hg => exact hg
    next hg => simp at h
  simp only [applicationGuard,Bool.and_eq_true,decide_eq_true_eq] at hg
  obtain ⟨⟨⟨hvf,hva⟩,hc⟩,ht⟩ := hg
  obtain ⟨⟨Γ,σ,f⟩,hf⟩ := (valid_iff cf).mp hvf
  obtain ⟨⟨Θ,υ,a⟩,ha⟩ := (valid_iff ca).mp hva
  subst cf; subst ca
  have hΓ : Γ=Θ := by
    have := congrArg (List.map SyntaxCode.decodeType) hc
    simpa only [encode,decode_types] using this
  cases hΓ
  have hσ : σ = .arrow υ (SyntaxCode.decodeType t) := by
    apply RawValidator.type_code_injective
    simpa [encode,SyntaxCode.typeCode,encode_type] using ht
  cases hσ
  have he := application_typed (τ:=SyntaxCode.decodeType t) f a
  rw [encode_type] at he
  rw [he] at h
  cases Option.some.inj h
  exact ⟨Γ,υ,SyntaxCode.decodeType t,f,a,encode_type t,rfl,rfl,rfl,input_roundtrip _⟩

theorem eraser_success (ca cb co : Code) (h : eraser ca cb = some co) :
    ∃ (Γ : List Ty) (a b : Input Γ .ground),
      encode ⟨Γ,.ground,a⟩=ca ∧ encode ⟨Γ,.ground,b⟩=cb ∧
      encode ⟨Γ,.ground,ScopedDAG.eraser a b⟩=co ∧
      decode co=some ⟨Γ,.ground,ScopedDAG.eraser a b⟩ := by
  have hg : eraserGuard ca cb = true := by
    unfold eraser at h
    split at h
    next hg => exact hg
    next hg => simp at h
  simp only [eraserGuard,Bool.and_eq_true,decide_eq_true_eq] at hg
  obtain ⟨⟨⟨⟨hva,hvb⟩,hc⟩,hta⟩,htb⟩ := hg
  obtain ⟨⟨Γ,σ,a⟩,ha⟩ := (valid_iff ca).mp hva
  obtain ⟨⟨Θ,τ,b⟩,hb⟩ := (valid_iff cb).mp hvb
  subst ca; subst cb
  have hΓ : Γ=Θ := by
    have := congrArg (List.map SyntaxCode.decodeType) hc
    simpa only [encode,decode_types] using this
  cases hΓ
  have hσ : σ=Ty.ground := RawValidator.type_code_injective hta
  have hτ : τ=Ty.ground := RawValidator.type_code_injective htb
  cases hσ; cases hτ
  rw [eraser_typed] at h
  cases Option.some.inj h
  exact ⟨Γ,a,b,rfl,rfl,rfl,input_roundtrip _⟩

theorem successReconstruction : RawCheckedCompositionTargets.SuccessReconstruction :=
  ⟨application_success,eraser_success⟩
end LogicLineages.ControlSensitivityCurrent.RawSourceDAG.CheckedComposition
