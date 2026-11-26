module

public import LogicLineages.NativeModule.PersistentMarking.NativeOrdinalArithmeticRealizationTargets
public import LogicLineages.NativeModule.PersistentMarking.NativeOrdinalArithmeticCompositionProof
public import LogicLineages.PersistentMarking.OrdinalArithmeticOrbitProof
public import LogicLineages.PersistentMarking.OrdinalOmegaOrbitProof

/-! Not a twin: new proof module (Opus B, round 3) for the drafted, proof-less target
`NativeOrdinalArithmeticRealizationTargets.NativeOrdinalArithmeticRealization`
(twin sha256 641f4a06…455d, frozen before this proof).  It instantiates the gated
`exact_LiteralNativeArithmeticRealizes` (generic composition #518 on the literal native
operators) at the ordinal orbits of `exact_OrdinalArithmeticOrbits` and the omega orbits
of `exact_OrdinalOmegaOrbits`, keeping the zero, successor, addition and multiplication
conjuncts. -/

@[expose] public section

namespace LogicLineages.PersistentMarking.NativeOrdinalArithmeticRealizationProof

theorem exact_NativeOrdinalArithmeticRealization :
    NativeOrdinalArithmeticRealizationTargets.NativeOrdinalArithmeticRealization := by
  intro S
  obtain ⟨wf, operations⟩ :=
    NativeOrdinalArithmeticCompositionProof.exact_LiteralNativeArithmeticRealizes S
  obtain ⟨Z, s, add, mul, equations⟩ := OrdinalArithmeticOrbitProof.exact_OrdinalArithmeticOrbits
  obtain ⟨w, one, pow, fix, omegaEquations, _⟩ :=
    OrdinalOmegaOrbitProof.exact_OrdinalOmegaOrbits Z s add mul equations
  obtain ⟨zero, successor, addition, multiplication, _⟩ :=
    operations Z s add mul w one pow fix equations omegaEquations
  exact ⟨wf, Z, s, add, mul, equations, zero, successor, addition, multiplication⟩

#print axioms exact_NativeOrdinalArithmeticRealization

end LogicLineages.PersistentMarking.NativeOrdinalArithmeticRealizationProof
