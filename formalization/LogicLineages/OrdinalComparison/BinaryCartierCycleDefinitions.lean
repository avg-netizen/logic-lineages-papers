module
public import LogicLineages.OrdinalComparison.BinaryPoleRemovalDefinitions
public import LogicLineages.OrdinalComparison.BinaryDenominatorProof
public import LogicLineages.OrdinalComparison.PolynomialDigitProof

@[expose] public section
namespace LogicLineages.OrdinalComparison

/-- The literal bounded numerator space, retaining the zero polynomial even
when the source denominator has degree zero. -/
abbrev ActualBinaryProperNumerator (d : Nat) :=
  {U : Polynomial (ZMod 2) // U.degree < (actualBinarySourceDimension d : WithBot Nat)}

noncomputable def actualBinaryProperNumeratorStep (d : Nat)
    (U : ActualBinaryProperNumerator d) : ActualBinaryProperNumerator d :=
  ⟨actualBinaryPolynomialDigit true (U.val * actualBinarySourceDenominator d),
    actualBinaryPolynomialStepDegree (ZMod 2) (actualBinarySourceDenominator d)
      U.val (actualBinarySourceDimension d)
      (actualBinarySourceDenominatorDegree d).le U.property true⟩

end LogicLineages.OrdinalComparison
