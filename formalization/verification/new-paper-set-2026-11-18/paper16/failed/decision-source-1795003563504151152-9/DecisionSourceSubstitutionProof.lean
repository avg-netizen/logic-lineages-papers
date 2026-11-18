import LogicLineages.PersistentMarking.DecisionSourceConstructProof
import LogicLineages.PersistentMarking.SpineSubstitutionProof
namespace LogicLineages.PersistentMarking.DecisionSourceSubstitutionProof
open Spine NameBridge TypeSupport DecisionInventory DecisionPorts DecisionSourceUniverse DecisionSourceBasicProof DecisionSourceConstructProof

mutual
 theorem preserves (K V H Γ) (Ξ Ω : BoundContext) (vs : Args) (d : Nat) (q : Expr) (τ : Ty)
    (hc : SubCompatible vs d Ξ Ω) (ht : Typed Ξ q τ) (hu : Universe K V H Γ q)
    (hv : ArgsUniverse K V H Γ vs) : Universe K V H Γ (substitute vs d q) := by
  cases q with
  | free σ x => exact hu
  | bound σ i =>
    by_cases hi : i < d
    · simpa only [substitute,if_pos hi] using hu
    · cases hl : vs.get (i-d) with
      | none =>
        simp only [substitute,if_neg hi,hl]
        exact hu
      | some v =>
        simp only [substitute,if_neg hi,hl]
        exact shiftUniverse K V H Γ d 0 v (getUniverse K V H Γ vs (i-d) v hv hl)
  | lam σ q =>
    cases ht with
    | lam hq =>
      have hp := SpineSubstitutionProof.compatiblePush vs d Ξ Ω hc σ
      have hr := preserves K V H Γ (Ξ.push σ) (Ω.push σ) vs (d+1) q _ hp hq (lamChild _ _ _ _ _ _ hu) hv
      have ha : (substitute vs (d+1) q).type = q.type :=
        (SpineShiftProof.annotationExact _ _ _ (SpineSubstitutionProof.preserves _ _ q _ vs (d+1) hq hp)).trans
          (SpineShiftProof.annotationExact _ _ _ hq).symm
      exact lamBuild K V H Γ σ _
        (fun υ hυ => hu.1 υ (List.mem_append_left _ (List.mem_append_left _ (by simpa only [ha] using hυ))))
        (fun υ hυ => hu.1 υ (List.mem_append_left _ (List.mem_append_right _ hυ))) hr
  | head f bs =>
    cases ht with
    | head hb =>
      exact headBuild K V H Γ f _
        (fun υ hυ => hu.1 υ (List.mem_append_left _ hυ)) (hu.2.1 f List.mem_cons_self)
        (basePreserves K V H Γ Ξ Ω vs d bs _ hc hb (headBase _ _ _ _ _ _ hu) hv)
  | marked f τ bs es =>
    cases ht with
    | marked hb he =>
      exact markedBuild K V H Γ f τ _ _
        (fun υ hυ => hu.1 υ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hυ))))
        (fun υ hυ => hu.1 υ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hυ))))
        (hu.2.1 f List.mem_cons_self)
        (basePreserves K V H Γ Ξ Ω vs d bs _ hc hb (markedBase _ _ _ _ _ _ _ _ hu) hv)
        (extrasPreserves K V H Γ Ξ Ω vs d es hc he (markedExtras _ _ _ _ _ _ _ _ hu) hv)
 termination_by sizeOf q
 theorem basePreserves (K V H Γ) (Ξ Ω : BoundContext) (vs : Args) (d : Nat) (qs : Args) (types : List Ty)
    (hc : SubCompatible vs d Ξ Ω) (ht : BaseTyped Ξ qs types) (hu : ArgsUniverse K V H Γ qs)
    (hv : ArgsUniverse K V H Γ vs) : ArgsUniverse K V H Γ (substituteArgs vs d qs) := by
  cases qs with
  | nil => trivial
  | cons q qs => cases ht with
    | cons hq hqs => exact ⟨preserves K V H Γ Ξ Ω vs d q _ hc hq hu.1 hv,basePreserves K V H Γ Ξ Ω vs d qs _ hc hqs hu.2 hv⟩
 termination_by sizeOf qs
 theorem extrasPreserves (K V H Γ) (Ξ Ω : BoundContext) (vs : Args) (d : Nat) (qs : Args)
    (hc : SubCompatible vs d Ξ Ω) (ht : ExtrasTyped Ξ qs) (hu : ArgsUniverse K V H Γ qs)
    (hv : ArgsUniverse K V H Γ vs) : ArgsUniverse K V H Γ (substituteArgs vs d qs) := by
  cases qs with
  | nil => trivial
  | cons q qs => cases ht with
    | cons hq hqs => exact ⟨preserves K V H Γ Ξ Ω vs d q _ hc hq hu.1 hv,extrasPreserves K V H Γ Ξ Ω vs d qs hc hqs hu.2 hv⟩
 termination_by sizeOf qs
end

theorem boundSubstitution : DecisionSourceTargets.SourceBoundSubstitution := by
  intro K V H Γ types vs q τ hq hv hu hvs
  exact preserves K V H Γ (BoundContext.prefix types EmptyContext) EmptyContext vs 0 q τ
    (SpineSubstitutionProof.finiteCompatible EmptyContext vs types hv) hq hu hvs
end LogicLineages.PersistentMarking.DecisionSourceSubstitutionProof
