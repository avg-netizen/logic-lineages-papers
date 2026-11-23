module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowPrimaryExchangeSoundArgs

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowPrimaryExchangeSoundProof
open NumberedWindowPrimaryExchange NumberedWindowPrimaryExchangeTargets
open NumberedWindowPrimaryExchangeSoundBasic NumberedWindowPrimaryExchangeSoundArgs

private theorem term {S K Q R} (h : ExchangeShape S K Q R) : TermUse S K Q R := by
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

theorem window : WindowExchangeSound := by
  intro S K C τ Q R h
  exact term h.1 C τ h.2.1.1 h.2.2.1

end LogicLineages.PersistentMarking.NumberedWindowPrimaryExchangeSoundProof
