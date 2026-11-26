module

public import LogicLineages.NativeModule.PersistentMarking.ConditionalUpperUniformTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

/-! Step (iii) of the uniform bridge: `tagTerm false (numeral x) = numeral (2x)` inside the
calculus, by induction on x from the accepted internal tag arithmetic (`doubleZero`,
`doubleSucc`, `congSuc`, `trans`). -/

@[expose] public section

namespace LogicLineages.PersistentMarking.ConditionalUpperUniformTagProof
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators PositiveArithmeticTransforms SourceComputabilityFormulaSupportProof
open ID1Completion.InternalCalculus ID1Completion.InternalTagArithmeticSyntaxProof
open ID1Completion.InternalTagArithmeticSupportProof
open ConditionalUpperUniformTargets

theorem numeralDouble {α : Type} (x : Nat) :
    (numeral (2 * (x + 1)) : OTerm α) = suc (suc (numeral (2 * x))) := by
  rw [Nat.mul_succ]
  rfl

/-- The derivation itself, by recursion on the numeral. -/
def evenTagNumeral (B : Positive (Fin 1)) {α : Type} :
    (x : Nat) → Derivation B ([] : List (Formula α)) (eqn (dbl (numeral x : OTerm α)) (numeral (2 * x)))
  | 0 => doubleZero
  | x + 1 => by
    rw [numeralDouble]
    exact trans (doubleSucc (numeral x)) (congSuc (congSuc (evenTagNumeral B x)))

theorem exact_EvenTagNumeral : EvenTagNumeral := by
  intro B α x
  refine ⟨?_⟩
  rw [ID1Completion.InternalSourceInversionSupportProof.onEquality]
  exact evenTagNumeral B (α := α) x

#print axioms exact_EvenTagNumeral

end LogicLineages.PersistentMarking.ConditionalUpperUniformTagProof
