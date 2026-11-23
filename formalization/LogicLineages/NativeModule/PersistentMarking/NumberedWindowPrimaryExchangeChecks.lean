module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowPrimaryExchangeReflectProof
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowPrimaryExchangeSoundProof

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowPrimaryExchangeChecks
open NumberedWindowPrimaryExchange NumberedWindowPrimaryExchangeBits
open NumberedWindowPrimaryExchangeTargets

theorem exact_HeadPairReflection : HeadPairReflection :=
  NumberedWindowPrimaryExchangeHeadProof.headPair

theorem exact_TermExchangeReflection : TermExchangeReflection :=
  NumberedWindowPrimaryExchangeReflectProof.term

theorem exact_ArgsExchangeReflection : ArgsExchangeReflection :=
  NumberedWindowPrimaryExchangeReflectProof.args

theorem exact_WindowExchangeReflection : WindowExchangeReflection := by
  intro S K C τ Q R
  simp only [windowExchangeBit,Bool.and_eq_true,exact_TermExchangeReflection S K Q R,
    NumberedWindowTypingBitsChecks.exact_WindowBit S K C τ Q,
    NumberedWindowTypingBitsChecks.exact_WindowBit S K C τ R,WindowExchange,and_assoc]

theorem exact_FiniteExchangeReflection : FiniteExchangeReflection := by
  intro S K Γ τ Q R
  unfold finiteExchangeBit
  rw [NumberedWindowFiniteBinderProof.lookup Γ]
  exact exact_WindowExchangeReflection S K _ τ Q R

theorem exact_ExchangePreservesAnnotations : ExchangePreservesAnnotations :=
  NumberedWindowPrimaryExchangeLawsProof.annotations

theorem exact_ExchangeSymmetric : ExchangeSymmetric :=
  NumberedWindowPrimaryExchangeLawsProof.symmetric

theorem exact_WindowExchangeSound : WindowExchangeSound :=
  NumberedWindowPrimaryExchangeSoundProof.window

#print axioms exact_HeadPairReflection
#print axioms exact_TermExchangeReflection
#print axioms exact_ArgsExchangeReflection
#print axioms exact_WindowExchangeReflection
#print axioms exact_FiniteExchangeReflection
#print axioms exact_ExchangePreservesAnnotations
#print axioms exact_ExchangeSymmetric
#print axioms exact_WindowExchangeSound

end LogicLineages.PersistentMarking.NumberedWindowPrimaryExchangeChecks
