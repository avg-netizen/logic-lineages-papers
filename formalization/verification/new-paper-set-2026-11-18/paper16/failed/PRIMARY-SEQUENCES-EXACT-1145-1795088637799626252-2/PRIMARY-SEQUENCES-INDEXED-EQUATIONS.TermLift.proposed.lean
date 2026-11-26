import LogicLineages.PersistentMarking.NumberedWindowPrimarySequenceTermTrace

namespace LogicLineages.PersistentMarking.NumberedWindowPrimarySequenceTermLift
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowPrimaryExchange
open NumberedWindowPrimarySequence

private def termMap {S K C D τ υ} (F : NTerm → NTerm)
    (hs : ∀ {Q R}, ExchangeShape S K Q R → ExchangeShape S K (F Q) (F R))
    (ht : ∀ {Q}, Typed C Q τ → Typed D (F Q) υ)
    {Q R} : TypedExchangeTrace S K C τ Q R →
      TypedExchangeTrace S K D υ (F Q) (F R)
  | .refl h => .refl (ht h)
  | .next h rest =>
    .next ⟨hs h.1,ht h.2.1,ht h.2.2⟩ (termMap F (@hs) (@ht) rest)

def underLam {S K C σ τ Q R} (p : TypedExchangeTrace S K (C.push σ) τ Q R) :
    TypedExchangeTrace S K C (.arrow σ τ) (.lam σ Q) (.lam σ R) :=
  termMap (NTerm.lam σ) (fun {Q R} h => .lam h) (fun {Q} h => .lam h) p

def inFunction {S K C σ τ Q R A} (p : TypedExchangeTrace S K C (.arrow σ τ) Q R)
    (ha : Typed C A σ) :
    TypedExchangeTrace S K C τ (.auxApp σ τ Q A) (.auxApp σ τ R A) :=
  termMap (fun X => .auxApp σ τ X A) (fun {Q R} h => .applicationFunction h)
    (fun {Q} h => .auxApp h ha) p

def inArgument {S K C σ τ Q A B} (hq : Typed C Q (.arrow σ τ))
    (p : TypedExchangeTrace S K C σ A B) :
    TypedExchangeTrace S K C τ (.auxApp σ τ Q A) (.auxApp σ τ Q B) :=
  termMap (NTerm.auxApp σ τ Q) (fun {A B} h => .applicationArgument h)
    (fun {A} h => .auxApp hq h) p

end LogicLineages.PersistentMarking.NumberedWindowPrimarySequenceTermLift
