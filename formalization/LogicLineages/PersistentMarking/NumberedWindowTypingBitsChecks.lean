import LogicLineages.PersistentMarking.NumberedWindowLiteralEqualityProof
import LogicLineages.PersistentMarking.NumberedWindowFiniteBinderProof
import LogicLineages.PersistentMarking.NumberedWindowTypingBitsTypingProof
import LogicLineages.PersistentMarking.NumberedWindowHeadEnumerationProof

namespace LogicLineages.PersistentMarking.NumberedWindowTypingBitsChecks
open NumberedWindowDomain NumberedWindowTypingBits NumberedWindowTypingBitsTargets

theorem exact_LiteralTermEquality : LiteralTermEquality :=
  NumberedWindowLiteralEqualityProof.term

theorem exact_LiteralArgsEquality : LiteralArgsEquality :=
  NumberedWindowLiteralEqualityProof.args

theorem exact_FiniteBinderLookup : FiniteBinderLookup :=
  NumberedWindowFiniteBinderProof.all

theorem exact_TypedBit : ExactTypedBit :=
  NumberedWindowTypingBitsTypingProof.typed

theorem exact_BaseBit : ExactBaseBit :=
  NumberedWindowTypingBitsTypingProof.base

theorem exact_ExtrasBit : ExactExtrasBit :=
  NumberedWindowTypingBitsTypingProof.extras

theorem exact_WindowBit : ExactWindowBit := by
  intro S K C τ Q
  simp only [windowBit,Bool.and_eq_true,exact_TypedBit,List.all_eq_true,
    decide_eq_true_eq,NumberedWindowHeadEnumerationProof.bit,InWindow,and_assoc]

theorem exact_FiniteWindowBit : ExactFiniteWindowBit := by
  intro S K Γ τ Q
  simp only [finiteWindowBit,exact_WindowBit,NumberedWindowFiniteBinderProof.lookup]

#print axioms exact_LiteralTermEquality
#print axioms exact_LiteralArgsEquality
#print axioms exact_FiniteBinderLookup
#print axioms exact_TypedBit
#print axioms exact_BaseBit
#print axioms exact_ExtrasBit
#print axioms exact_WindowBit
#print axioms exact_FiniteWindowBit

end LogicLineages.PersistentMarking.NumberedWindowTypingBitsChecks
