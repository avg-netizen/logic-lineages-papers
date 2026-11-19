import LogicLineages.PersistentMarking.NumberedWindowPrimarySequenceTermTrace
import LogicLineages.PersistentMarking.NumberedWindowPrimarySequenceArgsTrace

namespace LogicLineages.PersistentMarking.NumberedWindowPrimarySequenceConsLift
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowPrimaryExchange
open NumberedWindowPrimarySequence
open NumberedWindowPrimarySequenceTermTrace NumberedWindowPrimarySequenceArgsTrace

def argsFirstSite {S K C τ types Q R qs} :
    TypedExchangeTrace S K C τ Q R → BaseTyped C qs types →
      TypedArgsExchangeTrace S K C (τ::types) (.cons Q qs) (.cons R qs)
  | .refl h, hs => .refl (.cons h hs)
  | .next h rest, hs =>
    .next ⟨.first h.1,.cons h.2.1 hs,.cons h.2.2 hs⟩ (argsFirstSite rest hs)

def argsLaterSite {S K C τ types Q qs rs} (hq : Typed C Q τ) :
    TypedArgsExchangeTrace S K C types qs rs →
      TypedArgsExchangeTrace S K C (τ::types) (.cons Q qs) (.cons Q rs)
  | .refl h => .refl (.cons hq h)
  | .next h rest =>
    .next ⟨.later h.1,.cons hq h.2.1,.cons hq h.2.2⟩ (argsLaterSite hq rest)

theorem consNonempty {S K C τ types Q R qs rs}
    (p : Nonempty (TypedExchangeTrace S K C τ Q R))
    (q : Nonempty (TypedArgsExchangeTrace S K C types qs rs)) :
    Nonempty (TypedArgsExchangeTrace S K C (τ::types) (.cons Q qs) (.cons R rs)) := by
  obtain ⟨p⟩ := p
  obtain ⟨q⟩ := q
  exact ⟨argsAppend (argsFirstSite p (argsFirst q)) (argsLaterSite (termLast p) q)⟩

end LogicLineages.PersistentMarking.NumberedWindowPrimarySequenceConsLift
