module
public import LogicLineages.ControlSensitivityCurrent.RawDerivedCompositionTypedProof
public import LogicLineages.ControlSensitivityCurrent.RawCheckedCompositionSuccessProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.RawSourceDAG.DerivedComposition
open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source GroundEquivalence
open CheckedComposition

theorem pair_guard_success (ca cb : Code) (h : eraserGuard ca cb = true) :
    ∃ (Γ : List Ty) (a b : Input Γ .ground),
      encode ⟨Γ,.ground,a⟩=ca ∧ encode ⟨Γ,.ground,b⟩=cb := by
  have he : eraser ca cb=some (eraserRaw ca cb) := by simp [eraser,h]
  obtain ⟨Γ,a,b,ha,hb,_⟩ := eraser_success ca cb _ he
  exact ⟨Γ,a,b,ha,hb⟩

theorem detectors_success (ca cb : Code) (out : Code × Code)
    (h : detectors ca cb = some out) :
    ∃ (Γ : List Ty) (a b : Input Γ .ground),
      encode ⟨Γ,.ground,a⟩=ca ∧ encode ⟨Γ,.ground,b⟩=cb ∧
      out=(encode ⟨Γ,.ground,ScopedDAG.detectorLeft a b⟩,
        encode ⟨Γ,.ground,ScopedDAG.detectorRight a b⟩) ∧
      decode out.1=some ⟨Γ,.ground,ScopedDAG.detectorLeft a b⟩ ∧
      decode out.2=some ⟨Γ,.ground,ScopedDAG.detectorRight a b⟩ := by
  have hg : eraserGuard ca cb=true := by
    unfold detectors at h
    split at h
    next hg => exact hg
    next hg => simp at h
  obtain ⟨Γ,a,b,ha,hb⟩ := pair_guard_success ca cb hg
  subst ca; subst cb
  rw [detectors_typed] at h
  cases Option.some.inj h
  exact ⟨Γ,a,b,rfl,rfl,rfl,input_roundtrip _,input_roundtrip _⟩

theorem aggregate_guard_list (Γ : List Ty) (raw : List (Code × Code))
    (h : aggregateGuard (Γ.map SyntaxCode.typeCode) raw=true) :
    ∃ es : List (Input Γ .ground × Input Γ .ground),
      es.map (fun p => (encode ⟨Γ,.ground,p.1⟩,encode ⟨Γ,.ground,p.2⟩))=raw := by
  induction raw with
  | nil => exact ⟨[],rfl⟩
  | cons p raw ih =>
      rcases p with ⟨ca,cb⟩
      change ((eraserGuard ca cb && decide (ca.1=Γ.map SyntaxCode.typeCode)) &&
        aggregateGuard (Γ.map SyntaxCode.typeCode) raw)=true at h
      obtain ⟨⟨hg,hc⟩,ht⟩ := (by simpa only [Bool.and_eq_true,decide_eq_true_eq] using h)
      obtain ⟨Θ,a,b,ha,hb⟩ := pair_guard_success ca cb hg
      subst ca; subst cb
      have hΓ : Θ=Γ := by
        have := congrArg (List.map SyntaxCode.decodeType) hc
        simpa only [encode,decode_types] using this
      cases hΓ
      obtain ⟨es,hes⟩ := ih ht
      exact ⟨(a,b)::es,by simp only [List.map_cons,hes]⟩

theorem aggregate_success (context : List Nat) (raw : List (Code × Code))
    (out : Code × Code) (h : aggregate context raw=some out) :
    ∃ (Γ : List Ty) (es : List (Input Γ .ground × Input Γ .ground)),
      Γ.map SyntaxCode.typeCode=context ∧
      es.map (fun p => (encode ⟨Γ,.ground,p.1⟩,encode ⟨Γ,.ground,p.2⟩))=raw ∧
      out=(encode ⟨Γ,.ground,(ScopedDAG.aggregate es).1⟩,
        encode ⟨Γ,.ground,(ScopedDAG.aggregate es).2⟩) ∧
      decode out.1=some ⟨Γ,.ground,(ScopedDAG.aggregate es).1⟩ ∧
      decode out.2=some ⟨Γ,.ground,(ScopedDAG.aggregate es).2⟩ := by
  have hg : aggregateGuard context raw=true := by
    unfold aggregate at h
    split at h
    next hg => exact hg
    next hg => simp at h
  let Γ := context.map SyntaxCode.decodeType
  have hc : Γ.map SyntaxCode.typeCode=context := by
    simp [Γ,List.map_map,encode_type]
  obtain ⟨es,hes⟩ := aggregate_guard_list Γ raw (by simpa only [hc] using hg)
  have he := aggregate_typed es
  rw [hc,hes] at he
  rw [he] at h
  cases Option.some.inj h
  exact ⟨Γ,es,hc,hes,rfl,input_roundtrip _,input_roundtrip _⟩

theorem wrap_success (upper : Bool) (c out : Code) (h : wrap upper c=some out) :
    ∃ (Γ : List Ty) (a : Input Γ .ground), encode ⟨Γ,.ground,a⟩=c ∧
      out=encode ⟨Γ,.ground,if upper then upperInput a else lowerInput a⟩ ∧
      decode out=some ⟨Γ,.ground,if upper then upperInput a else lowerInput a⟩ := by
  have hg : wrapperGuard c=true := by
    unfold wrap at h
    split at h
    next hg => exact hg
    next hg => simp at h
  obtain ⟨hv,ht⟩ := (by simpa only [wrapperGuard,Bool.and_eq_true,decide_eq_true_eq] using hg)
  obtain ⟨⟨Γ,σ,a⟩,ha⟩ := (valid_iff c).mp hv
  subst c
  have hs : σ=Ty.ground := RawValidator.type_code_injective ht
  cases hs
  rw [wrap_typed] at h
  cases Option.some.inj h
  exact ⟨Γ,a,rfl,rfl,input_roundtrip _⟩

theorem successReconstruction : RawDerivedCompositionTargets.SuccessReconstruction :=
  ⟨detectors_success,aggregate_success,wrap_success⟩
end LogicLineages.ControlSensitivityCurrent.RawSourceDAG.DerivedComposition
