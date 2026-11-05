module
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.CircuitBridgeDefinitions
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.CircuitLinearTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.CircuitBridgeTargets
open CircuitLinear Narendran SourcePolynomialRealization SourceFiniteExponentProjection

def ExpressionMeaning : Prop := ∀ (n : Nat) (x : Fin n → ZPolynomial) (d : SignedPair.Expression n),
  (expressionPolynomial x d).toFinsupp = polynomialMeaning (fun i => (x i).toFinsupp) d

/-- Every occurrence of every well-formed row is preserved by the codec,
including repeated indices and signed coefficients. -/
def RowMeaning : Prop := ∀ (n : Nat) (p : Nat → NPolynomial) (r : Row),
  (∀ m ∈ r, ∀ i, m.2.2 = some i → i < n) →
  expressionPolynomial (fun i : Fin n => signed (p i.val))
    (SignedPair.fromMonomials (r.filterMap (monomialOfCode n))) = rowPolynomial p r

/-- Exact correspondence for the actual shared N[X] system language, not the
unrelated integer-polynomial/Nat-root language. Well-formedness is explicit. -/
def RawSystemFaithful : Prop := ∀ c : SystemCode, WellFormedCode c →
  (PolynomialSatisfiable (systemOfCode c) ↔ ∃ p : Nat → NPolynomial, RowsSolve p c.2)

def CircuitSystemWellFormed : Prop :=
  ∀ c : LogicLineages.ComputabilityKnowledge.CircuitReduction.Circuit, c.WellFormed →
    WellFormedCode (encodeCircuitSystem c)

end LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.CircuitBridgeTargets
