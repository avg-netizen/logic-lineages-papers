module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowPrimarySequenceTargets

@[expose] public section

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

def termAppend {S K C τ Q R T} :
    TypedExchangeTrace S K C τ Q R → TypedExchangeTrace S K C τ R T →
      TypedExchangeTrace S K C τ Q T
  | .refl _, q => q
  | .next h rest, q => .next h (termAppend rest q)

def termReverse {S K C τ Q R} :
    TypedExchangeTrace S K C τ Q R → TypedExchangeTrace S K C τ R Q
  | .refl ht => .refl ht
  | .next h rest => termAppend (termReverse rest) (termOne ⟨termSymm h.1,h.2.2,h.2.1⟩)

end LogicLineages.PersistentMarking.NumberedWindowPrimarySequenceTermTrace
