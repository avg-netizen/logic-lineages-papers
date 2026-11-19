import LogicLineages.PersistentMarking.NumberedWindowClosingRawCases

namespace LogicLineages.PersistentMarking.NumberedWindowClosingRawProof
open NumberedWindowSyntax NumberedWindowClosing NumberedWindowRules
open NumberedWindowClosingOperationsProof (copies)
open NumberedWindowClosingShiftProof (freshBody)
open NumberedWindowClosingRawCases (replacement selection toBottom)
open NameBridge (Name)

theorem term (n : Name) {S K q r} (h : RawStep S K q r) :
    ∀ d, RawStep S K (closeAt n d q) (closeAt n d r) := by
  induction h using RawStep.rec
    (motive_2 := fun qs rs _ => ∀ d, RawArgsStep S K (closeArgsAt n d qs) (closeArgsAt n d rs)) with
  | mark => intro d; exact .mark
  | lower => intro d; exact .lower
  | select hg ht ha => intro d; exact selection n d hg ht ha
  | copy hp hg =>
    intro d
    simp only [closeAt,copies]
    exact .copy hp hg
  | stat he hg hr => intro d; exact .stat he hg (replacement n d hr)
  | fabs =>
    intro d
    simp only [closeAt,freshBody]
    exact .fabs
  | beta => intro d; exact NumberedWindowClosingRawCases.beta n d
  | bottom hn => intro d; exact toBottom n d hn
  | lam _ ih => intro d; exact .lam (ih (d+1))
  | ordinaryBase _ ih => intro d; exact .ordinaryBase (ih d)
  | numberedBase _ ih => intro d; exact .numberedBase (ih d)
  | numberedExtra _ ih => intro d; exact .numberedExtra (ih d)
  | auxFunction _ ih => intro d; exact .auxFunction (ih d)
  | first _ ih => intro d; exact .first (ih d)
  | later _ ih => intro d; exact .later (ih d)

end LogicLineages.PersistentMarking.NumberedWindowClosingRawProof
