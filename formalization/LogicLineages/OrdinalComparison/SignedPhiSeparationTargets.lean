module
public import LogicLineages.OrdinalComparison.SignedPhiSeparationDefinitions
public import LogicLineages.OrdinalComparison.SignedShiftCollectionTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.SignedPhiSeparation.Targets
open SignedShiftCollection

/-- D remains the least offset for ALL original occurrences. For nonempty
support the integer maximum is exact: D = max(0, -min ORIGINAL shift), so
this is precisely max(0, -min ORIGINAL shift, A+1-B), not a larger bound.
The empty original row has D = 0; every all-cancelled row uses delta = D.
All original arguments are safe, with exact integer and rebased values. -/
def ExactSourceShiftAndArguments : Prop := ∀ row : Row,
  (∀ d : Nat, domainOffset row ≤ d ↔
    ∀ a ∈ row, 0 ≤ (d : Int) + a.2) ∧
  domainOffset row ≤ delta row ∧
  (collected row = [] → delta row = domainOffset row) ∧
  (collected row ≠ [] →
    (delta row : Int) = max (domainOffset row : Int)
      ((lowerMass row : Int) + 1 - greatestShift row)) ∧
  (∀ a ∈ row, ∀ x : Nat,
    0 ≤ (x : Int) + (delta row : Int) + a.2 ∧
    (argument (shiftedInput row x) a.2 : Int) =
      (x : Int) + (delta row : Int) + a.2 ∧
    argument (shiftedInput row x) a.2 =
      rebasedInput row x + rebaseKey row a.2)

/-- Exact equality with the actual collection at the exact shifted input,
zero in the all-cancelled case, and the literal leading/lower decomposition.
No arbitrary evaluator, unproved collection oracle, or sign premise is used. -/
def ExactEvaluationAndCancellation : Prop := ∀ row : Row,
  (∀ x : Nat,
    value row (shiftedInput row x) =
      CommonHeadCollectedRow.weighted
        (fun k => (Phi (rebasedInput row x + k) : Int)) (collected row)) ∧
  (collected row = [] → ∀ x : Nat, value row (shiftedInput row x) = 0) ∧
  (collected row ≠ [] → ∀ x : Nat,
    value row (shiftedInput row x) =
      leadingCoefficient row *
        (Phi (argument (shiftedInput row x) (greatestShift row)) : Int) +
      CommonHeadCollectedRow.weighted
        (fun k => (Phi (rebasedInput row x + k) : Int)) (lowerRow row))

/-- Strict separation by the actual Phi at EVERY natural input, using only
the sign of the actual nonzero leading coefficient and the exact source delta.
Empty/all-cancelled rows have only the preceding zero conclusion. -/
def ActualSignedPhiSeparation : Prop := ∀ row : Row, collected row ≠ [] →
  (0 < leadingCoefficient row → ∀ x : Nat,
    (Phi x : Int) < value row (shiftedInput row x)) ∧
  (leadingCoefficient row < 0 → ∀ x : Nat,
    value row (shiftedInput row x) < -(Phi x : Int))

/-- Uniform primitive recursion of the displayed algorithms themselves:
the accepted nine signed-collection maps (including B and its coefficient),
the exact lower row/A/delta, original and shifted evaluation/argument maps.
This is not a first-order arithmetic decision procedure. -/
def UniformPrimitiveRecursiveData : Prop :=
  SignedShiftCollection.Targets.UniformPrimitiveRecursiveData ∧
  Primrec lowerRow ∧
  Primrec lowerMass ∧
  Primrec delta ∧
  Primrec₂ argument ∧
  Primrec₂ value ∧
  Primrec₂ shiftedInput ∧
  Primrec₂ rebasedInput ∧
  Primrec₂ originalArguments ∧
  Primrec₂ shiftedArguments ∧
  Primrec₂ (fun row x => value row (shiftedInput row x))

end LogicLineages.OrdinalComparison.SignedPhiSeparation.Targets
