module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowPrimarySequenceElementarySound
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowPrimarySequenceOrderedClosure

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowPrimarySequenceSound
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowPrimary
open NumberedWindowPrimarySequence
open NumberedWindowPrimarySequenceOrderedClosure

theorem term {S K C τ Q R} (p : TypedExchangeTrace S K C τ Q R) :
    Primary S K C τ Q R := by
  induction p with
  | refl h => exact .refl h
  | next h _ ih => exact .trans (NumberedWindowPrimarySequenceElementarySound.term h) ih

theorem args {S K C types qs rs} (p : TypedArgsExchangeTrace S K C types qs rs) :
    OrderedPrimary S K C types qs rs := by
  induction p with
  | refl h => exact orderedRefl _ _ _ _ _ h
  | next h _ ih =>
    exact orderedTrans _ _ _ _ _ _ _ (NumberedWindowPrimarySequenceElementarySound.args h) ih

theorem admitted {S K C τ Q R} (p : AdmittedExchangeTrace S K C τ Q R) :
    Primary S K C τ Q R := by
  induction p with
  | refl h => exact .refl h.1
  | next h _ ih =>
    exact .trans (NumberedWindowPrimaryExchangeChecks.exact_WindowExchangeSound _ _ _ _ _ _ h) ih

end LogicLineages.PersistentMarking.NumberedWindowPrimarySequenceSound
