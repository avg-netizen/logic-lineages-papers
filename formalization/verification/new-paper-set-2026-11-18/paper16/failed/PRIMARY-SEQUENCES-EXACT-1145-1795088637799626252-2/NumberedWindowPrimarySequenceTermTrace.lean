import LogicLineages.PersistentMarking.NumberedWindowPrimarySequenceTargets

namespace LogicLineages.PersistentMarking.NumberedWindowPrimarySequenceTermTrace
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowPrimaryExchange
open NumberedWindowPrimarySequence
open NumberedWindowPrimaryExchangeLawsProof (termSymm)

theorem termFirst {S K C τ Q R} (p : TypedExchangeTrace S K C τ Q R) : Typed C Q τ := by
  cases p with
  | refl h => exact h
  | next h _ => exact h.2.1

theorem termLast {S K C τ Q R} (p : TypedExchangeTrace S K C τ Q R) : Typed C R τ := by
  induction p with
  | refl h => exact h
  | next _ _ ih => exact ih

def termOne {S K C τ Q R} (h : TypedExchange S K C τ Q R) :
    TypedExchangeTrace S K C τ Q R :=
  .next h (.refl h.2.2)

def termAppend {S K C τ Q R T} (p : TypedExchangeTrace S K C τ Q R)
    (q : TypedExchangeTrace S K C τ R T) : TypedExchangeTrace S K C τ Q T := by
  cases p with
  | refl _ => exact q
  | next h rest => exact .next h (termAppend rest q)
termination_by structural p

def termReverse {S K C τ Q R} (p : TypedExchangeTrace S K C τ Q R) :
    TypedExchangeTrace S K C τ R Q := by
  cases p with
  | refl ht => exact .refl ht
  | next h rest =>
    exact termAppend (termReverse rest) (termOne ⟨termSymm h.1,h.2.2,h.2.1⟩)
termination_by structural p

end LogicLineages.PersistentMarking.NumberedWindowPrimarySequenceTermTrace
