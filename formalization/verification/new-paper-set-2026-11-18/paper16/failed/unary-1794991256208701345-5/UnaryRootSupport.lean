import LogicLineages.PersistentMarking.UnarySelectionProof
namespace LogicLineages.PersistentMarking.UnaryRootSupport
open Spine UnaryTransportSupport

theorem argumentFacts {S : Signature} {a b : Expr} (h : ExtendedWeak S a b) : PaperTerm S a a.type ∧ PaperTerm S b b.type := by
  obtain ⟨h⟩ := h
  have hf := ExtendedEndpointProof.weakFacts h
  exact ⟨hf.1,hf.2.1⟩

theorem headPaper {S : Signature} {f : Head} {base : Args} {a : Expr} {τ : Ty}
    (hp : PaperTerm S (.head f base) f.result) (ha : PaperTerm S a a.type) :
    PaperTerm S (.marked f τ base (.cons a .nil)) τ :=
  newOwner S f f.result τ a.type base .nil a (RefinementMarkProof.markPaper S _ _ _ hp rfl) ha

theorem markedPaper {S : Signature} {f : Head} {σ : Ty} {base extras : Args} {a : Expr} {τ : Ty}
    (hp : PaperTerm S (.marked f σ base extras) σ) (ha : PaperTerm S a a.type) :
    PaperTerm S (.marked f τ base (extras.append (.cons a .nil))) τ := newOwner S f σ τ a.type base extras a hp ha

theorem resultPaper {S : Signature} {t p r b : Expr} {σ τ : Ty}
    (ht : PaperTerm S t σ) (hcall : CallTyped EmptyContext t.type (.cons b .nil) τ)
    (hr : apply t (.cons b .nil) = some r) (he : ExtendedWeak S p r) : PaperTerm S r τ := by
  have hty := SpineShiftProof.annotationExact _ _ _ ht.1
  have ht' : Typed EmptyContext t t.type := hty.symm ▸ ht.1
  have hout := SpineCallTypingProof.callPreserves EmptyContext t t.type (.cons b .nil) τ r ht' hcall hr
  obtain ⟨he⟩ := he
  exact ⟨hout,(ExtendedEndpointProof.weakFacts he).2.1.2⟩
end LogicLineages.PersistentMarking.UnaryRootSupport
