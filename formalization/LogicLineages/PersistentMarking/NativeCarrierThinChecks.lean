import LogicLineages.PersistentMarking.NativeCarrierLiftProof

namespace LogicLineages.PersistentMarking.NativeCarrierThinChecks
open Spine NativeReduction NativeTypingProof TypeSupport NativeCarrierTargets NativeCarrierTypingProof

theorem markedInput (S : Signature) (B : Ty) (K U T : Expr)
    (h : Strict S (W B K U) T) : Weak S (Q B K U B) T := by
  cases h with
  | intro hp ht hm hw =>
    have he := Option.some.inj (hm.symm.trans (markW B K U))
    simpa only [he] using hw

theorem inside (B : Ty) (K U : Expr) : Included K (W B K U) := by
  have hK : Included K (lifted K) := by
    intro τ hτ
    exact List.mem_append_right _ hτ
  intro τ hτ
  exact leftIncluded B B _ U τ (rightIncluded (stepType B) (.arrow B B) _ (lifted K) τ (hK τ hτ))

private theorem appSupport (σ τ : Ty) (f a : Expr) (ρ : Ty) :
    ρ ∈ support (app σ τ f a) ↔ ρ ∈ subtypes τ ∨ ρ ∈ support f ∨ ρ ∈ support a := by
  simp only [app,support,Head.result,supportArgs,List.mem_append,List.not_mem_nil,or_false]

theorem supportApp (B : Ty) (P K U T : Expr) (hP : Included P K) (hT : Included T (W B K U)) :
    Included (app B B P T) (W B K U) := by
  intro τ hτ
  rcases (appSupport B B P T τ).mp hτ with h | h | h
  · exact TypeSupportFoundationProof.rootSupport (W B K U) τ h
  · exact inside B K U τ (hP τ h)
  · exact hT τ h

theorem exact_Carrier : Carrier := by
  intro S B P K U hP hK hU hKP hSupport
  have hFam := family S B K U hK.1.1 hU.1.1
  have hOrd := ordinary B K U hK.1.2.1 hU.1.2.1
  constructor
  · exact ⟨⟨B,hFam.w,hU.1.1,hOrd,hU.1.2.1⟩,
      .intro hFam.w hU.1.1 (markW B K U) (NativeCarrierSelectionProof.toU S B K U hK.1.1 hU.1.1 hU.1.2.1),
      rightIncluded B B _ U⟩
  · intro T hT hTSupport hBelow
    have hTarget := appPaper S B B P T hP.1.1 hT.1
    have hToP := NativeCarrierLiftProof.toFunction S B P K U hK.1.1 hP.1.1 hFam hKP
    have hToT := NativeCarrierSelectionProof.toTarget S B K U T hFam hT.1 (markedInput S B K U T hBelow.2.1)
    have hPType := SpineShiftProof.annotationExact _ _ _ hP.1.1.1
    have hTType := SpineShiftProof.annotationExact _ _ _ hT.1.1
    have hwhole : Whole S (.recursor B) .nil (c0Extras B K U) (.cons P (.cons T .nil)) :=
      .cons (by rw [hPType]; exact hToP) (.cons (by rw [hTType]; exact hToT) .nil)
    have hHead : Precedes S (.recursor B) (.app B B) := ⟨1,0,rfl,rfl,by decide⟩
    have hCarrier : Weak S (C₀ B K U B) (app B B P T) := .copy (hFam.c0 B) hTarget hHead hwhole
    exact ⟨⟨B,hFam.w,hTarget,hOrd,appOrdinary B B P T hP.1.2.1 hT.2.1⟩,
      .intro hFam.w hTarget (markW B K U)
        (NativeCarrierSelectionProof.prefixSelections S B K U _ hK.1.1 hFam hTarget hCarrier),
      supportApp B P K U T hSupport hTSupport⟩

#print axioms exact_Carrier
end LogicLineages.PersistentMarking.NativeCarrierThinChecks
