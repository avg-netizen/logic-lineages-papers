import LogicLineages.PersistentMarking.NumberedWindowPrimarySequenceTargets

namespace LogicLineages.PersistentMarking.NumberedWindowPrimarySequenceArgsTrace
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowPrimarySequence

theorem argsFirst {S K C types qs rs} (p : TypedArgsExchangeTrace S K C types qs rs) :
    BaseTyped C qs types := by
  cases p with
  | refl h => exact h
  | next h _ => exact h.2.1

theorem argsLast {S K C types qs rs} (p : TypedArgsExchangeTrace S K C types qs rs) :
    BaseTyped C rs types := by
  induction p with
  | refl h => exact h
  | next _ _ ih => exact ih

def argsAppend {S K C types qs rs ts} :
    TypedArgsExchangeTrace S K C types qs rs → TypedArgsExchangeTrace S K C types rs ts →
      TypedArgsExchangeTrace S K C types qs ts
  | .refl _, q => q
  | .next h rest, q => .next h (argsAppend rest q)

end LogicLineages.PersistentMarking.NumberedWindowPrimarySequenceArgsTrace
