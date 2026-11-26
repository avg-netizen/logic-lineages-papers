import LogicLineages.PersistentMarking.NumberedWindowPrimarySequenceTargets

namespace LogicLineages.PersistentMarking.NumberedWindowPrimarySequenceElementarySound
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowPrimary
open NumberedWindowPrimaryExchange
open NumberedWindowPrimaryExchangeSoundBasic NumberedWindowPrimaryExchangeSoundArgs
open NumberedWindowPrimarySequence NumberedWindowPrimarySequenceTargets

/- The checked one-site reconstruction builders need only actual typing
at the two endpoints; lexical support is paid separately on the trace. -/
theorem terms {S K Q R} (h : ExchangeShape S K Q R) : TermUse S K Q R := by
  induction h using ExchangeShape.rec (motive_2 := fun qs rs _ => ArgsUse S K qs rs) with
  | ordinary hp e hperm => exact ordinaryRoot hp e hperm
  | numbered hp hperm => exact numberedRoot hp hperm
  | lam _ ih => exact underLam ih
  | ordinaryBase _ ih => exact ordinaryBase ih
  | numberedBase _ ih => exact numberedBase ih
  | numberedExtra hargs ih => exact numberedExtra hargs ih
  | applicationFunction _ ih => exact inFunction ih
  | applicationArgument _ ih => exact inArgument ih
  | first _ ih => first | exact firstSite ih | apply firstSite ih <;> assumption
  | later _ ih => first | exact laterSite ih | apply laterSite ih <;> assumption

private theorem argsFixed (S : Spine.Signature) (K : List Ty) (qs rs : NArgs)
    (h : ArgsExchangeShape S K qs rs) : ArgsUse S K qs rs := by
  cases qs with
  | nil => cases h
  | cons Q qs =>
    cases h with
    | first hq => exact firstSite (terms hq)
    | later ht => exact laterSite (argsFixed S K qs _ ht)
termination_by structural qs

theorem term {S K C τ Q R} (h : TypedExchange S K C τ Q R) :
    Primary S K C τ Q R :=
  terms h.1 C τ h.2.1 h.2.2

theorem args {S K C types qs rs} (h : TypedArgsExchange S K C types qs rs) :
    OrderedPrimary S K C types qs rs :=
  argsFixed S K qs rs h.1 C types h.2.1 h.2.2

theorem both : TypedElementarySound :=
  ⟨fun _ _ _ _ _ _ h => term h,fun _ _ _ _ _ _ h => args h⟩

end LogicLineages.PersistentMarking.NumberedWindowPrimarySequenceElementarySound
