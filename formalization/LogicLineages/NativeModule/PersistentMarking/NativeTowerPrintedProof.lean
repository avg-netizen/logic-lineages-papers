module

public import LogicLineages.NativeModule.PersistentMarking.NativeTowerPrintedTargets
public import LogicLineages.NativeModule.PersistentMarking.NativeTowerProof
public import LogicLineages.NativeModule.PersistentMarking.NativeOrdinalArithmeticCompositionProof

@[expose] public section

/-! The printed towers: `NativeTowerRealization` at the printed native `fix`, whose realization of
`Fix` is `exact_LiteralNativeArithmeticRealizes` (#1456 closure). -/

namespace LogicLineages.PersistentMarking.NativeTowerPrintedProof
open NativeTowerTargets NativeTowerPrintedTargets NativeOrdinalArithmeticCompositionTargets

theorem exact_PrintedTowerRealization : PrintedTowerRealization := by
  intro S
  obtain ⟨_, arithmetic⟩ := NativeOrdinalArithmeticCompositionProof.exact_LiteralNativeArithmeticRealizes S
  obtain ⟨wf, tower⟩ := NativeTowerProof.exact_NativeTowerRealization S
  refine ⟨wf, ?_⟩
  intro Z s add mul w one pow fix h1 h2 l
  have hfix := (arithmetic Z s add mul w one pow fix h1 h2).2.2.2.2.2.2.2.1
  exact tower (literalArithmetic S).fix fix hfix l

#print axioms exact_PrintedTowerRealization

end LogicLineages.PersistentMarking.NativeTowerPrintedProof
