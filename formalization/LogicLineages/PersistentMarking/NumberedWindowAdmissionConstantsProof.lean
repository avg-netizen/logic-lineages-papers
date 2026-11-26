import LogicLineages.PersistentMarking.NumberedWindowAdmissionTargets
import LogicLineages.PersistentMarking.NumberedWindowArithmeticAtomCodeChecks
import LogicLineages.PersistentMarking.NumberedWindowHeadEnumerationChecks

namespace LogicLineages.PersistentMarking.NumberedWindowAdmissionConstantsProof
open NumberedWindowAdmissionTargets NumberedWindowArithmeticTyCode NumberedWindowArithmeticHeadCode
open NumberedWindowHeadEnumerationTargets (headBit)
open NumberedWindowArithmeticAtomCodeChecks
open TypeSupport (subtypes)

theorem types (S : Spine.Signature) (K : List Ty) (τ : Ty) :
    (window S K).1.contains (encodeTy τ) = typesIn K (subtypes τ) := by
  have root : τ ∈ subtypes τ := by cases τ <;> simp [subtypes]
  have codeInject : Function.Injective encodeTy := by
    intro s t h
    have hr := exact_TyCodec.2.1 s
    rw [h,exact_TyCodec.2.1 t] at hr
    exact (Option.some.inj hr).symm
  apply Bool.eq_iff_iff.mpr
  rw [List.contains_iff_mem]
  change encodeTy τ ∈ (K.filter (fun σ => typesIn K (subtypes σ))).map encodeTy ↔ _
  rw [List.mem_map]
  constructor
  · rintro ⟨s,hs,he⟩
    rw [← codeInject he]
    exact (List.mem_filter.mp hs).2
  · intro h
    have incl : ∀ a ∈ subtypes τ, decide (a ∈ K) = true := List.all_eq_true.mp h
    exact ⟨τ,List.mem_filter.mpr ⟨of_decide_eq_true (incl τ root),h⟩,rfl⟩

theorem heads (S : Spine.Signature) (K : List Ty) (f : Head) :
    (window S K).2.contains (encodeHead f) = headBit S K f := by
  have codeInject : Function.Injective encodeHead := by
    intro g h he
    have hr := exact_HeadCodec.2.1 g
    rw [he,exact_HeadCodec.2.1 h] at hr
    exact (Option.some.inj hr).symm
  apply Bool.eq_iff_iff.mpr
  rw [List.contains_iff_mem]
  change encodeHead f ∈ (NumberedWindowHeadEnumerationTargets.admittedHeads S K).map encodeHead ↔ _
  rw [List.mem_map,NumberedWindowHeadEnumerationChecks.exact_HeadBit]
  constructor
  · rintro ⟨g,hg,he⟩
    rw [← codeInject he]
    exact ((NumberedWindowHeadEnumerationChecks.exact_AdmittedHeadEnumeration S K).2 _).mp hg
  · intro hf
    exact ⟨f,((NumberedWindowHeadEnumerationChecks.exact_AdmittedHeadEnumeration S K).2 _).mpr hf,rfl⟩

theorem constants : WindowConstants := ⟨types,heads⟩
end LogicLineages.PersistentMarking.NumberedWindowAdmissionConstantsProof
