import LogicLineages.PersistentMarking.NumberedWindowPrimaryExchangeSoundBasic

namespace LogicLineages.PersistentMarking.NumberedWindowPrimaryExchangeSoundArgs
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowPrimary
open NumberedWindowPrimaryExchange NumberedWindowPrimaryExchangeSoundBasic
open NumberedWindowPrimaryExchangeLawsProof (argsType)
open NumberedWindowTypingBits (annotationList)
open NumberedWindowTypingBitsArgsProof (extrasBase)

private theorem orderedRefl (S : Spine.Signature) (K : List Ty) (C : Spine.BoundContext)
    (qs : NArgs) (types : List Ty) (h : BaseTyped C qs types) :
    OrderedPrimary S K C types qs qs := by
  cases qs with
  | nil => cases h; exact .nil
  | cons Q qs =>
    cases h with
    | cons hq hs => exact .cons (.refl hq) (orderedRefl S K C qs _ hs)
termination_by structural qs

theorem ordinaryBase {S K f bs cs} (ih : ArgsUse S K bs cs) :
    TermUse S K (.ordinary f bs) (.ordinary f cs) := by
  intro C output hq hr
  cases hq with
  | ordinary hb =>
    cases hr with
    | ordinary hc => exact .ordinaryArguments (ih _ _ hb hc)

theorem numberedBase {S K f τ k bs cs es} (ih : ArgsUse S K bs cs) :
    TermUse S K (.numbered f τ k bs es) (.numbered f τ k cs es) := by
  intro C output hq hr
  cases hq with
  | numbered hb he =>
    cases hr with
    | numbered hc _ => exact .numberedBase (ih _ _ hb hc) he

theorem numberedExtra {S K f τ k bs es ds} (h : ArgsExchangeShape S K es ds)
    (ih : ArgsUse S K es ds) :
    TermUse S K (.numbered f τ k bs es) (.numbered f τ k bs ds) := by
  intro C output hq hr
  cases hq with
  | numbered hb he =>
    cases hr with
    | numbered _ hd =>
      have hd' : BaseTyped C ds (annotationList es) := (argsType h).symm ▸ extrasBase hd
      exact .numberedExtras hb (ih _ _ (extrasBase he) hd')

theorem firstSite {S K Q R qs} (ih : TermUse S K Q R) :
    ArgsUse S K (.cons Q qs) (.cons R qs) := by
  intro C types hq hr
  cases hq with
  | cons hQ hs =>
    cases hr with
    | cons hR _ => exact .cons (ih _ _ hQ hR) (orderedRefl _ _ _ _ _ hs)

theorem laterSite {S K Q qs rs} (ih : ArgsUse S K qs rs) :
    ArgsUse S K (.cons Q qs) (.cons Q rs) := by
  intro C types hq hr
  cases hq with
  | cons hQ hs =>
    cases hr with
    | cons hR ht => exact .cons (.refl hQ) (ih _ _ hs ht)

end LogicLineages.PersistentMarking.NumberedWindowPrimaryExchangeSoundArgs
