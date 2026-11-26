module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowPrimarySequenceArgsTrace

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowPrimarySequenceBaseLift
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowPrimaryExchange
open NumberedWindowPrimarySequence
open NumberedWindowTypingBitsArgsProof (baseShape)

def fromArgs {S K C types τ} (F : NArgs → NTerm)
    (hs : ∀ {qs rs}, ArgsExchangeShape S K qs rs → ExchangeShape S K (F qs) (F rs))
    (ht : ∀ {qs}, BaseTyped C qs types → Typed C (F qs) τ)
    {qs rs} : TypedArgsExchangeTrace S K C types qs rs →
      TypedExchangeTrace S K C τ (F qs) (F rs)
  | .refl h => .refl (ht h)
  | .next h rest =>
    .next ⟨hs h.1,ht h.2.1,ht h.2.2⟩ (fromArgs F (@hs) (@ht) rest)

def underOrdinary {S K C f qs rs}
    (p : TypedArgsExchangeTrace S K C f.arguments qs rs) :
    TypedExchangeTrace S K C f.result (.ordinary f qs) (.ordinary f rs) :=
  fromArgs (NTerm.ordinary f) (fun {qs rs} h => .ordinaryBase h)
    (fun {qs} h => .ordinary h) p

def underNumberedBase {S K C f τ k qs rs es}
    (p : TypedArgsExchangeTrace S K C f.arguments qs rs) (he : ExtrasTyped C es) :
    TypedExchangeTrace S K C τ (.numbered f τ k qs es) (.numbered f τ k rs es) :=
  fromArgs (fun xs => .numbered f τ k xs es) (fun {qs rs} h => .numberedBase h)
    (fun {qs} h => .numbered h he) p

def underNumberedExtras {S K C f τ k bs es ds types}
    (hb : BaseTyped C bs f.arguments) (p : TypedArgsExchangeTrace S K C types es ds) :
    TypedExchangeTrace S K C τ (.numbered f τ k bs es) (.numbered f τ k bs ds) :=
  fromArgs (NTerm.numbered f τ k bs) (fun {es ds} h => .numberedExtra h)
    (fun {es} h => .numbered hb (baseShape h).2) p

end LogicLineages.PersistentMarking.NumberedWindowPrimarySequenceBaseLift
