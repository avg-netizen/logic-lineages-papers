module

public import LogicLineages.NativeModule.PersistentMarking.TypeSupportNamedProof

@[expose] public section

namespace LogicLineages.PersistentMarking.TypeSupportConfinementProof
open Spine NameBridge StructuralContext TypeSupport TypeSupportFoundationProof

theorem substitutionConfinement : TypeSupportTargets.SubstitutionConfinement := by
  intro S s t τ θ hs ht hos hot hin hfv hθ ρ h
  have hs' := TypeSupportSubstitutionProof.exactSubstitution S s τ θ hs hos hθ ρ
  have ht' := TypeSupportSubstitutionProof.exactSubstitution S t τ θ ht hot hθ ρ
  apply hs'.mpr
  rcases ht'.mp h with h | ⟨σ,x,hx,hi⟩
  · exact Or.inl (hin ρ h)
  · exact Or.inr ⟨σ,x,hfv (σ,x) hx,hi⟩

theorem supportAppend (xs ys : Args) : supportArgs (xs.append ys) = supportArgs xs ++ supportArgs ys := by
  cases xs with
  | nil => rfl
  | cons q qs => simp only [Args.append,supportArgs,supportAppend qs ys,List.append_assoc]
termination_by sizeOf xs

theorem contextConfinement : TypeSupportTargets.ContextConfinement := by
  intro S C σ τ s t hc hs ht hos hot hin
  induction hc with
  | hole => exact hin
  | head hc hf hb hvb hob ha hva hoa hargs ih =>
    intro ρ h
    simp only [fill,support,supportAppend,supportArgs,List.mem_append,or_assoc] at h ⊢
    rcases h with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl (ih hs ht ρ h)))
    · exact Or.inr (Or.inr (Or.inr h))
  | @bind inside σ τ name hc ih =>
    have hst := SpineShiftProof.annotationExact _ _ _ (StructuralFillProof.fillPaper S inside σ τ s hc hs).1
    have htt := SpineShiftProof.annotationExact _ _ _ (StructuralFillProof.fillPaper S inside σ τ t hc ht).1
    have hsc := FreeCallProof.annotation (closingMap name) (closingAnnotation name) 0 (fill inside s)
    have htc := FreeCallProof.annotation (closingMap name) (closingAnnotation name) 0 (fill inside t)
    intro ρ h
    simp only [fill,support,close,hsc,htc,hst,htt,closing,List.mem_append,or_assoc] at h ⊢
    rcases h with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (ih hs ht ρ h))

theorem fullConfinementStability : TypeSupportTargets.FullConfinementStability :=
  ⟨substitutionConfinement,contextConfinement⟩

theorem namedContextConfinement : TypeSupportTargets.NamedContextConfinement := by
  intro S C σ τ s t hc hs hvs hos ht hvt hot hin ρ h
  have hsmall : Included (encode [] t) (encode [] s) := by
    intro υ hu
    rw [encodingSupport] at hu ⊢
    exact hin υ hu
  have hh := contextConfinement S (encodeContext C) σ τ (encode [] s) (encode [] t)
    (StructuralCoverageProof.contextCoverage S C σ τ hc)
    ⟨BridgeTypingProof.encodeTyped [] s σ hs,(BridgeTypingProof.encodeValidity S [] s).mp hvs⟩
    ⟨BridgeTypingProof.encodeTyped [] t σ ht,(BridgeTypingProof.encodeValidity S [] t).mp hvt⟩
    ((StructuralCoverageProof.encodeOrdinary [] s).mp hos) ((StructuralCoverageProof.encodeOrdinary [] t).mp hot) hsmall
  have hencoded : ρ ∈ support (fill (encodeContext C) (encode [] t)) := by
    rw [← ClosingNamedProof.namedFill C t,encodingSupport]
    exact h
  have he := hh ρ hencoded
  rw [← ClosingNamedProof.namedFill C s,encodingSupport] at he
  exact he
end LogicLineages.PersistentMarking.TypeSupportConfinementProof
