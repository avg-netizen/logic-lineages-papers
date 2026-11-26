import LogicLineages.PersistentMarking.UnaryTransportProof
import LogicLineages.PersistentMarking.SourceSuccessProof
import LogicLineages.PersistentMarking.SuccessfulStagesProof
namespace LogicLineages.PersistentMarking.ApplicationCovarianceProof
open Spine

theorem consTyped {σ τ : Ty} {a : Expr} {args : Args}
    (h : CallTyped EmptyContext σ (.cons a args) τ) :
    ∃ α β, σ = .arrow α β ∧ Typed EmptyContext a α ∧ CallTyped EmptyContext β args τ := by
  cases h with
  | cons ha hr => exact ⟨_,_,rfl,ha,hr⟩

theorem foldTransport (S : Signature) (q s : Expr) (as bs : Args) (τ : Ty) (r : Expr)
    (he : ExtendedWeak S q s) (hargs : ExtendedOrderedTree S as bs)
    (hqa : CallTyped EmptyContext q.type as τ) (hsb : CallTyped EmptyContext s.type bs τ)
    (hr : unaryCalls s bs = some r) :
    ∃ p, unaryCalls q as = some p ∧ ExtendedWeak S p r := by
  cases as with
  | nil =>
    cases hargs
    simp only [unaryCalls,Option.some.injEq] at hr
    subst r
    exact ⟨q,by simp only [unaryCalls],he⟩
  | cons a rest =>
    cases hargs with
    | @orderedCons a b rest tail hab htail =>
      have heFacts : PaperTerm S q q.type ∧ PaperTerm S s s.type ∧ q.type = s.type := by
        obtain ⟨he⟩ := he
        exact ExtendedEndpointProof.weakFacts he
      obtain ⟨α,β,hqType,hat,hrest⟩ := consTyped hqa
      obtain ⟨γ,δ,hsType,hbt,htailTyped⟩ := consTyped hsb
      have hArrow : Ty.arrow α β = .arrow γ δ := hqType.symm.trans (heFacts.2.2.trans hsType)
      have hdomains : α = γ ∧ β = δ := Ty.arrow.inj hArrow
      rcases hdomains with ⟨rfl,rfl⟩
      have hqaOne : CallTyped EmptyContext q.type (.cons a .nil) β := by rw [hqType]; exact .cons hat .nil
      have hsbOne : CallTyped EmptyContext s.type (.cons b .nil) β := by rw [hsType]; exact .cons hbt .nil
      cases hone : apply s (.cons b .nil) with
      | none => simp [unaryCalls,hone] at hr
      | some u =>
        have hrestResult : unaryCalls u tail = some r := by simpa only [unaryCalls,hone,Option.bind_some] using hr
        obtain ⟨p,hp,hpu⟩ := UnaryTransportProof.unaryTransport S q s a b β u he ⟨hab⟩ hqaOne hsbOne hone
        have hpt := SpineCallTypingProof.callPreserves EmptyContext q q.type (.cons a .nil) β p heFacts.1.1 hqaOne hp
        have hut := SpineCallTypingProof.callPreserves EmptyContext s s.type (.cons b .nil) β u heFacts.2.1.1 hsbOne hone
        have hptType := SpineShiftProof.annotationExact _ _ _ hpt
        have hutType := SpineShiftProof.annotationExact _ _ _ hut
        have hpa : CallTyped EmptyContext p.type rest τ := hptType.symm ▸ hrest
        have hub : CallTyped EmptyContext u.type tail τ := hutType.symm ▸ htailTyped
        obtain ⟨out,hout,hE⟩ := foldTransport S p u rest tail τ r hpu htail hpa hub hrestResult
        refine ⟨out,?_,hE⟩
        simp only [unaryCalls,hp,Option.bind_some,hout]
termination_by sizeOf as

theorem fullApplication : ApplicationCovarianceTargets.FullApplication := by
  intro S q s as bs τ r he hargs hqa hsb hr
  obtain ⟨p,hp⟩ := SourceSuccessProof.sourceSuccess S q s as bs τ r he hargs hqa hsb hr
  have hleft := SuccessfulStagesProof.successfulUnaryStages q as p hp
  have hright := SuccessfulStagesProof.successfulUnaryStages s bs r hr
  obtain ⟨hargs⟩ := hargs
  obtain ⟨p',hp',hE⟩ := foldTransport S q s as bs τ r he hargs hqa hsb hright
  have heq : p = p' := Option.some.inj (hleft.symm.trans hp')
  subst p'
  exact ⟨p,hp,hE⟩
end LogicLineages.PersistentMarking.ApplicationCovarianceProof
