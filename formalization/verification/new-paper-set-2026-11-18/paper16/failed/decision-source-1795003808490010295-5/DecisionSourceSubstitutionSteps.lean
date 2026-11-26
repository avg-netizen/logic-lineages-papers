import LogicLineages.PersistentMarking.DecisionSourceConstructProof
import LogicLineages.PersistentMarking.SpineSubstitutionProof
namespace LogicLineages.PersistentMarking.DecisionSourceSubstitutionProof
open Spine NameBridge TypeSupport DecisionInventory DecisionPorts DecisionSourceUniverse DecisionSourceBasicProof DecisionSourceConstructProof

theorem boundLeaf (K V H Γ) (vs : Args) (d : Nat) (σ : Ty) (i : Nat)
    (hu : Universe K V H Γ (.bound σ i)) (hv : ArgsUniverse K V H Γ vs) :
    Universe K V H Γ (substitute vs d (.bound σ i)) := by
  by_cases hi : i < d
  · simpa only [substitute,if_pos hi] using hu
  · cases hl : vs.get (i-d) with
    | none => simp only [substitute,if_neg hi,hl]; exact hu
    | some v =>
      simp only [substitute,if_neg hi,hl]
      exact shiftUniverse K V H Γ d 0 v (getUniverse K V H Γ vs (i-d) v hv hl)

theorem lambdaStep (K V H Γ) (Ξ Ω : BoundContext) (vs : Args) (d : Nat) (σ : Ty) (q : Expr) (τ : Ty)
    (hc : SubCompatible vs d Ξ Ω) (ht : Typed (Ξ.push σ) q τ)
    (hu : Universe K V H Γ (.lam σ q))
    (hr : Universe K V H Γ (substitute vs (d+1) q)) :
    Universe K V H Γ (substitute vs d (.lam σ q)) := by
  have hp := SpineSubstitutionProof.compatiblePush vs d Ξ Ω hc σ
  have ha : (substitute vs (d+1) q).type = q.type :=
    (SpineShiftProof.annotationExact _ _ _ (SpineSubstitutionProof.preserves _ _ q τ vs (d+1) ht hp)).trans
      (SpineShiftProof.annotationExact _ _ _ ht).symm
  exact lamBuild K V H Γ σ _
    (fun υ hυ => hu.1 υ (List.mem_append_left _ (List.mem_append_left _ (by simpa only [ha] using hυ))))
    (fun υ hυ => hu.1 υ (List.mem_append_left _ (List.mem_append_right _ hυ))) hr

theorem headStep (K V H Γ f bs vs d)
    (hu : Universe K V H Γ (.head f bs))
    (hr : ArgsUniverse K V H Γ (substituteArgs vs d bs)) :
    Universe K V H Γ (substitute vs d (.head f bs)) :=
  headBuild K V H Γ f _ (fun υ hυ => hu.1 υ (List.mem_append_left _ hυ))
    (hu.2.1 f List.mem_cons_self) hr

theorem markedStep (K V H Γ f τ bs es vs d)
    (hu : Universe K V H Γ (.marked f τ bs es))
    (hb : ArgsUniverse K V H Γ (substituteArgs vs d bs))
    (he : ArgsUniverse K V H Γ (substituteArgs vs d es)) :
    Universe K V H Γ (substitute vs d (.marked f τ bs es)) :=
  markedBuild K V H Γ f τ _ _
    (fun υ hυ => hu.1 υ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hυ))))
    (fun υ hυ => hu.1 υ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hυ))))
    (hu.2.1 f List.mem_cons_self) hb he

end LogicLineages.PersistentMarking.DecisionSourceSubstitutionProof
