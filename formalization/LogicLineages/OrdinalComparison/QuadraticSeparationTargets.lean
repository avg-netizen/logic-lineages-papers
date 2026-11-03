module
public import LogicLineages.OrdinalComparison.QuadraticSeparationDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.QuadraticSeparation.Targets

/-- Literal quantitative V separation. Signed indices and required iteration
length may vary with the input; only the source displayed inequality is assumed.
Both source depths are genuinely positive, not artifacts of Int.toNat. -/
def UniformQuadraticSeparation : Prop := ∀ (w : Nat) (j k : Int) (R : Nat),
  Region w j k R →
  0 < signedDepth k w ∧ 0 < signedDepth j (w + 1) ∧
  (Phi^[R]) (rawQuadraticShift k w) < rawQuadraticShift j (w + 1)

/-- Exact signed-index order at one input on the actual positive-depth domain.
Outside that domain raw totalization can identify distinct negative exponents;
no claim is made there. No kernel-recursion hypothesis is used. -/
def ExactSameInputOrder : Prop := ∀ (w : Nat) (j k : Int),
  0 < signedDepth j w → 0 < signedDepth k w →
  (rawQuadraticShift j w < rawQuadraticShift k w ↔ j < k) ∧
  (rawQuadraticShift j w = rawQuadraticShift k w ↔ j = k) ∧
  (rawQuadraticShift j w ≤ rawQuadraticShift k w ↔ j ≤ k)

end LogicLineages.OrdinalComparison.QuadraticSeparation.Targets
