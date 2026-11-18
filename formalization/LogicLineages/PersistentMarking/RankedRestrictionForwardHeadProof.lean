import LogicLineages.PersistentMarking.RankedRestrictionForwardTargets
import LogicLineages.PersistentMarking.RankedRestrictionPrecedenceProof

namespace LogicLineages.PersistentMarking.RankedRestrictionForwardHeadProof
open Spine RankedRestrictionTargets RankedRestrictionSyntaxProof RankedRestrictionMatchingProof
open RankedRestrictionForwardTargets

theorem var (S : Signature) (σ : Ty) (x : Nat) : WeakMotive S (.free σ x) (.free σ x) := by
  constructor
  · intro hs _
    cases σ with
    | ground => exact Or.inr .var
    | arrow => cases hs.2
  · intro f bs h
    cases h

theorem abs (S : Signature) (σ : Ty) (s t : Expr) : WeakMotive S (.lam σ s) (.lam σ t) := by
  constructor
  · intro hs
    cases hs.2
  · intro f bs h
    cases h

theorem funHead (S : Signature) (f g : Head) (bs ts : Args) (hEq : Equivalent S f g)
    (ih : MatchingMotive S bs ts) : WeakMotive S (.head f bs) (.head g ts) := by
  constructor
  · intro hf hg
    have hh := RankedRestrictionPrecedenceProof.sameHead S f g hf.2.1 hg.2.1 hEq
    subst g
    have hMatch := ih (baseAt S f bs hf) (baseAt S f ts hg)
    rcases either S hMatch with hStrict | hEqual
    · obtain ⟨kept,removed,matched,added,hBs,hTs,hN,hE,hC⟩ := hStrict
      exact Or.inl (.multiset hBs hTs hN hE hC (headDominates S f bs ts hMatch))
    · exact Or.inr (.head hEqual)
  · intro f' bs' h
    cases h

theorem put (S : Signature) (f : Head) (bs : Args) (t : Expr)
    (ih : WeakMotive S (.marked f f.result bs .nil) t) : WeakMotive S (.head f bs) t := by
  constructor
  · intro hs ht
    have hTy : f.result = .ground := annotation _ hs.2
    exact Or.inl (ih.2 f bs (by rw [hTy]) hs ht)
  · intro f' bs' h
    cases h

theorem select (S : Signature) (f : Head) (τ : Ty) (bs es : Args) (t q r : Expr) (i : Nat) (ds : List Ty)
    (ha : At bs i q ∨ At es i q) (hq : Typed EmptyContext q (ArrowPrefix ds τ))
    (hc : apply q (ownerCopies f bs es ds) = some r) (ih : WeakMotive S r t) :
    WeakMotive S (.marked f τ bs es) t := by
  constructor
  · intro hs
    cases hs.2
  · intro f' bs' hShape hs ht
    obtain ⟨rfl,rfl,rfl,rfl⟩ := Expr.marked.inj hShape
    have hAt : At bs i q := by
      rcases ha with hb | he
      · exact hb
      · cases he
    have hTerm := baseAt S f bs hs i q hAt
    have hAnn := (annotation q hTerm.2).symm.trans (SpineShiftProof.annotationExact _ _ _ hq)
    cases ds with
    | nil =>
      have hr : q=r := Option.some.inj hc
      subst r
      rcases ih.1 hTerm ht with hR | hE
      · exact .subtermStrict hAt hR
      · exact .subtermEq hAt hE
    | cons α ds => cases hAnn

theorem fabs (S : Signature) (f : Head) (σ τ : Ty) (bs es : Args) (body : Expr) :
    WeakMotive S (.marked f (.arrow σ τ) bs es) (.lam σ body) := by
  constructor
  · intro hs
    cases hs.2
  · intro f' bs' h
    have he := (Expr.marked.inj h).2.1
    cases he

theorem copy (S : Signature) (f g : Head) (bs es ts : Args) (hP : Precedes S f g)
    (ih : WholeMotive S f bs es ts) : WeakMotive S (.marked f g.result bs es) (.head g ts) := by
  constructor
  · intro hs
    cases hs.2
  · intro f' bs' h hs ht
    obtain ⟨rfl,_,rfl,rfl⟩ := Expr.marked.inj h
    exact .precedence hP (ih rfl hs (baseAt S g ts ht))

theorem stat (S : Signature) (f g : Head) (bs es ts : Args) (hE : Equivalent S f g)
    (ih : MultisetMotive S bs ts) (ih' : WholeMotive S f bs es ts) :
    WeakMotive S (.marked f g.result bs es) (.head g ts) := by
  constructor
  · intro hs
    cases hs.2
  · intro f' bs' h hs ht
    obtain ⟨rfl,_,rfl,rfl⟩ := Expr.marked.inj h
    have hf := RankedRestrictionPrecedenceProof.sameHead S f g hs.2.1 ht.2.1 hE
    subst g
    have hArgs := baseAt S f ts ht
    obtain ⟨kept,removed,matched,added,hB,hT,hN,hEqual,hCover⟩ := ih (baseAt S f bs hs) hArgs
    exact .multiset hB hT hN hEqual hCover (ih' rfl hs hArgs)

theorem strict (S : Signature) (q t r : Expr) (h : mark q = some r) (ih : WeakMotive S r t) :
    StrictMotive S q t := by
  intro hs ht
  cases q with
  | free σ x => cases h
  | bound | lam | marked => cases hs.2
  | head f bs => exact ih.2 f bs (Option.some.inj (h.symm.trans (markEq S f bs hs))) hs ht

end LogicLineages.PersistentMarking.RankedRestrictionForwardHeadProof
