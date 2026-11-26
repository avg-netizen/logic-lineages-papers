module

public import LogicLineages.NativeModule.PersistentMarking.ApplicationCovarianceTargets
public import LogicLineages.NativeModule.PersistentMarking.TwoEnvironmentProof
public import LogicLineages.NativeModule.PersistentMarking.SharpAdmissibleProof
public import LogicLineages.NativeModule.PersistentMarking.PrefixEscapeProof

@[expose] public section

namespace LogicLineages.PersistentMarking.UnaryTransportSupport
open Spine NameBridge AuxiliaryReflexivityProof RefinementAppendProof

theorem headCall {f : Head} {base : Args} {a : Expr} {τ : Ty}
    (h : CallTyped EmptyContext (Expr.head f base).type (.cons a .nil) τ) :
    apply (.head f base) (.cons a .nil) = some (.marked f τ base (.cons a .nil)) := by
  have hc := SpineCallTypingProof.consumeExact _ _ _ _ h
  simp only [Expr.type] at hc
  simpa only [apply,applyAux,SubstitutionProof.emptyArgsSubstitution,hc,Option.map_some]

theorem markedCall {f : Head} {σ : Ty} {base extras : Args} {a : Expr} {τ : Ty}
    (h : CallTyped EmptyContext (Expr.marked f σ base extras).type (.cons a .nil) τ) :
    apply (.marked f σ base extras) (.cons a .nil) = some (.marked f τ base (extras.append (.cons a .nil))) := by
  have hc := SpineCallTypingProof.consumeExact _ _ _ _ h
  simp only [Expr.type] at hc
  simpa only [apply,applyAux,SubstitutionProof.emptyArgsSubstitution,hc,Option.map_some]

theorem lamArgument {σ : Ty} {body a : Expr} {τ : Ty}
    (h : CallTyped EmptyContext (Expr.lam σ body).type (.cons a .nil) τ) : Typed EmptyContext a σ := by
  cases h with | cons ha hr => exact ha

theorem lamCall {σ : Ty} {body a : Expr} {τ : Ty}
    (h : CallTyped EmptyContext (Expr.lam σ body).type (.cons a .nil) τ) :
    apply (.lam σ body) (.cons a .nil) = some (substitute (.cons a .nil) 0 body) := by
  have ha := SpineShiftProof.annotationExact _ _ _ (lamArgument h)
  simp only [apply,applyAux,ha,if_true]

theorem replaceRelated (S : Signature) (σ : Ty) (x : Nat) (a b : Expr) (h : ExtendedWeak S a b) :
    TwoEnvironmentTargets.Related S (RefinementCallMapProof.replace σ x a) (RefinementCallMapProof.replace σ x b) := by
  intro τ y
  by_cases he : (τ,y) = (σ,x)
  · simpa only [RefinementCallMapProof.replace,he,if_true] using h
  · simp only [RefinementCallMapProof.replace,he,if_false]; exact ⟨.var⟩

theorem openedReplace (σ : Ty) (x : Nat) (a body : Expr) (hf : freeOccurs (σ,x) body = false) :
    freeSub (RefinementCallMapProof.replace σ x a) 0 (openBody σ x body) = substitute (.cons a .nil) 0 body := by
  have hc := FreeCompositionProof.composition (RefinementCallMapProof.replace σ x a) (.cons (.free σ x) .nil) 0 body
  simpa only [openBody,freeSubArgs,freeSub,RefinementCallMapProof.replace,ite_true,SubstitutionProof.shiftZero,
    Args.length,Nat.zero_add,RefinementCallMapProof.absent σ x a 1 body hf] using hc

theorem appendWhole {S : Signature} {f : Head} {base extras xs ys : Args}
    (hx : ExtendedWholeTree S f base extras xs) (hy : ExtendedWholeTree S f base extras ys) :
    _root_.Nonempty (ExtendedWholeTree S f base extras (xs.append ys)) := by
  cases xs with
  | nil => exact ⟨hy⟩
  | cons x xs =>
    cases hx with
    | wholeCons h ht =>
      obtain ⟨ht'⟩ := appendWhole ht hy
      exact ⟨.wholeCons h ht'⟩
termination_by sizeOf xs

theorem appendOrdered {S : Signature} {xs ys as bs : Args}
    (hx : ExtendedOrderedTree S xs ys) (ha : ExtendedOrderedTree S as bs) :
    _root_.Nonempty (ExtendedOrderedTree S (xs.append as) (ys.append bs)) := by
  cases xs with
  | nil => cases hx; exact ⟨ha⟩
  | cons x xs =>
    cases hx with
    | orderedCons h ht =>
      obtain ⟨ht'⟩ := appendOrdered ht ha
      exact ⟨.orderedCons h ht'⟩
termination_by sizeOf xs

theorem wholeDrop {S : Signature} {f : Head} {τ : Ty} {base extras added ts : Args}
    (hp : PaperTerm S (.marked f τ base (extras.append added)) τ)
    (h : ExtendedWholeTree S f base extras ts) :
    _root_.Nonempty (ExtendedWholeTree S f base (extras.append added) ts) := by
  cases ts with
  | nil => exact ⟨.wholeNil⟩
  | cons t ts =>
    cases h with
    | wholeCons hw ht =>
      have ht' := (ExtendedEndpointProof.weakFacts hw).2.1
      have hp' := retypePaper S f τ t.type base (extras.append added) hp
      obtain ⟨hs⟩ := wholeDrop hp ht
      exact ⟨.wholeCons (.drop hp' ht' hw) hs⟩
termination_by sizeOf ts

theorem newOwner (S : Signature) (f : Head) (ρ τ σ : Ty) (base extras : Args) (a : Expr)
    (hp : PaperTerm S (.marked f ρ base extras) ρ) (ha : PaperTerm S a σ) :
    PaperTerm S (.marked f τ base (extras.append (.cons a .nil))) τ :=
  appendPaper S f ρ τ base extras (.cons a .nil) hp (.cons ha.1 .nil) ⟨ha.2,True.intro⟩

theorem newExtra {S : Signature} {f : Head} {τ : Ty} {base extras : Args} {a b : Expr}
    (hp : PaperTerm S (.marked f τ base (extras.append (.cons a .nil))) τ) (hab : ExtendedWeak S a b) :
    ExtendedWeak S (.marked f b.type base (extras.append (.cons a .nil))) b := by
  obtain ⟨hab⟩ := hab
  have hf := ExtendedEndpointProof.weakFacts hab
  have hat : Typed EmptyContext a b.type := hf.2.2 ▸ hf.1.1
  obtain ⟨i,hi⟩ := atRight extras (show At (.cons a .nil) 0 a from .here)
  exact ⟨.select (domains := []) (retypePaper S f τ b.type base _ hp) hf.2.1 (Or.inr hi) hat rfl hab⟩

theorem wholeNewExtra {S : Signature} {f : Head} {τ : Ty} {base extras ts : Args} {a b : Expr}
    (hp : PaperTerm S (.marked f τ base (extras.append (.cons a .nil))) τ)
    (h : ExtendedWholeTree S f base extras ts) (hab : ExtendedWeak S a b) :
    _root_.Nonempty (ExtendedWholeTree S f base (extras.append (.cons a .nil)) (ts.append (.cons b .nil))) := by
  obtain ⟨hold⟩ := wholeDrop hp h
  obtain ⟨hnew⟩ := newExtra hp hab
  exact appendWhole hold (.wholeCons hnew .wholeNil)

end LogicLineages.PersistentMarking.UnaryTransportSupport
