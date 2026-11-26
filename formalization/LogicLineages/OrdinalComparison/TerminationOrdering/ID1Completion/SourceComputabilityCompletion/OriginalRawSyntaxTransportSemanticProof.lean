module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportWeightProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportSemanticProof
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportWeightProof

/-- Independent native recursion on the ORIGINAL raw numeric tree. It does not
mention the Program AST, any machine run, a fuel value, source typing or C/I. -/
def semanticFold (mode : Mode) (d k raw : Nat) : Nat :=
  if h1 : arityValue raw = 1 then
    rebuildValue mode raw
      (semanticFold mode d (if tagValue raw = 1 then k + 1 else k) (firstValue raw)) 0
  else if h2 : arityValue raw = 2 then
    rebuildValue mode raw (semanticFold mode d k (firstValue raw)) (semanticFold mode d k (secondValue raw))
  else leafValue mode d k raw
termination_by raw
decreasing_by
  · have hb := unaryChildBound raw h1
    omega
  · have hb := binaryChildrenBound raw h2
    omega
  · have hb := binaryChildrenBound raw h2
    omega

 theorem semanticEquation (mode : Mode) (d k raw : Nat) :
    semanticFold mode d k raw =
      if arityValue raw = 1 then rebuildValue mode raw
        (semanticFold mode d (if tagValue raw = 1 then k + 1 else k) (firstValue raw)) 0
      else if arityValue raw = 2 then rebuildValue mode raw
        (semanticFold mode d k (firstValue raw)) (semanticFold mode d k (secondValue raw))
      else leafValue mode d k raw := by
  rw [semanticFold]
  split_ifs <;> rfl

/-- Exact visit-and-return cost, independent of output values and all variable
parameters. This is used to prove successful execution, not merely terminality. -/
def semanticCost (raw : Nat) : Nat :=
  if h1 : arityValue raw = 1 then 1 + semanticCost (firstValue raw) + 1
  else if h2 : arityValue raw = 2 then 1 + semanticCost (firstValue raw) + semanticCost (secondValue raw) + 1
  else 1
termination_by raw
decreasing_by
  · have hb := unaryChildBound raw h1
    omega
  · have hb := binaryChildrenBound raw h2
    omega
  · have hb := binaryChildrenBound raw h2
    omega

 theorem costEquation (raw : Nat) : semanticCost raw =
    if arityValue raw = 1 then 1 + semanticCost (firstValue raw) + 1
    else if arityValue raw = 2 then 1 + semanticCost (firstValue raw) + semanticCost (secondValue raw) + 1
    else 1 := by
  rw [semanticCost]
  split_ifs <;> rfl

 theorem costPositive (raw : Nat) : 0 < semanticCost raw := by
  rw [costEquation]
  split_ifs <;> omega

 theorem costFuelBound (raw : Nat) : semanticCost raw ≤ fuelValue raw := by
  induction raw using Nat.strong_induction_on with
  | h raw ih =>
    rw [costEquation]
    by_cases h1 : arityValue raw = 1
    · rw [if_pos h1]
      have hb := unaryChildBound raw h1
      have hc := ih (firstValue raw) (by omega)
      have hf := unaryFuelBound raw h1
      omega
    · rw [if_neg h1]
      by_cases h2 : arityValue raw = 2
      · rw [if_pos h2]
        have hb := binaryChildrenBound raw h2
        have hc1 := ih (firstValue raw) (by omega)
        have hc2 := ih (secondValue raw) (by omega)
        have hf := binaryFuelBound raw h2
        omega
      · rw [if_neg h2]
        simp only [fuelValue]
        omega

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportSemanticProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportSemanticProof
