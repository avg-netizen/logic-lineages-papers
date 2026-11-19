import LogicLineages.PersistentMarking.NumberedWindowPrimaryExchangeLawsProof

namespace LogicLineages.PersistentMarking.NumberedWindowPrimaryExchangeSoundBasic
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowPrimary
open NumberedWindowPrimaryExchange

abbrev TermUse (S : Spine.Signature) (K : List Ty) (Q R : NTerm) : Prop :=
  ∀ C τ, Typed C Q τ → Typed C R τ → Primary S K C τ Q R

abbrev ArgsUse (S : Spine.Signature) (K : List Ty) (qs rs : NArgs) : Prop :=
  ∀ C types, BaseTyped C qs types → BaseTyped C rs types → OrderedPrimary S K C types qs rs

theorem ordinaryRoot {S K f g bs cs} (h : AllowedHeadPair S K f g)
    (e : f.result = g.result) (hp : bs.toList.Perm cs.toList) :
    TermUse S K (.ordinary f bs) (.ordinary g cs) := by
  intro C τ hq hr
  cases hq with
  | ordinary hb =>
    have ht : Typed C (.ordinary g cs) g.result := e ▸ hr
    cases ht with
    | ordinary hc => exact .ordinary h.1 h.2.1 h.2.2 e hb hc hp

theorem numberedRoot {S K f g τ k bs cs es} (h : AllowedHeadPair S K f g)
    (hp : bs.toList.Perm cs.toList) :
    TermUse S K (.numbered f τ k bs es) (.numbered g τ k cs es) := by
  intro C output hq hr
  cases hq with
  | numbered hb he =>
    cases hr with
    | numbered hc _ => exact .numbered h.1 h.2.1 h.2.2 hb hc he hp

theorem underLam {S K σ Q R} (ih : TermUse S K Q R) :
    TermUse S K (.lam σ Q) (.lam σ R) := by
  intro C output hq hr
  cases hq with
  | lam hb =>
    cases hr with
    | lam hc => exact .lam (ih _ _ hb hc)

theorem inFunction {S K σ τ Q R A} (ih : TermUse S K Q R) :
    TermUse S K (.auxApp σ τ Q A) (.auxApp σ τ R A) := by
  intro C output hq hr
  cases hq with
  | auxApp hb ha =>
    cases hr with
    | auxApp hc _ => exact .appFunction (ih _ _ hb hc) ha

theorem inArgument {S K σ τ Q A B} (ih : TermUse S K A B) :
    TermUse S K (.auxApp σ τ Q A) (.auxApp σ τ Q B) := by
  intro C output hq hr
  cases hq with
  | auxApp hQ ha =>
    cases hr with
    | auxApp _ hb => exact .appArgument hQ (ih _ _ ha hb)

end LogicLineages.PersistentMarking.NumberedWindowPrimaryExchangeSoundBasic
