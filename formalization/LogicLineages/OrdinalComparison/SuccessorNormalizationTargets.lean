module
public import LogicLineages.OrdinalComparison.SuccessorNormalizationDefinitions
public import Mathlib.Computability.Partrec

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

def SuccessorNormalizationProgramsPrimitiveRecursive : Prop :=
  Primrec (fun p : Nat × Nat × SuccessorNormalizationState =>
    encodedSuccessorNormalizationStep p.1 p.2.1 p.2.2) ∧
  Primrec (fun p : Nat × Nat × Nat × Nat × Nat =>
    encodedSuccessorNormalizationTrace p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) ∧
  Primrec (fun p : Nat × Nat × Nat × Nat =>
    encodedSuccessorNormalization p.1 p.2.1 p.2.2.1 p.2.2.2)

/-- ENTIRE finite mixed-successor OUTER NORMALIZATION pass of source section8:
actual final source shape, no-jump stop at equal exponent or a higher limit,
fixed norm-ball preservation for every retained kernel, computably accumulated
dynamic domains, and exact equality of norm output AND replacement counts.
This does not assert the remaining comparison/certificate recursive children. -/
def ActualSuccessorNormalizationProgram : Prop :=
  SuccessorNormalizationProgramsPrimitiveRecursive ∧
  ∀ (w : List (NONote × Nat)) (E : FixedLimitPositiveExpr) (eta lower : NONote) (c : Nat),
    oneVariableComparisonValid (.range (w++[(eta,c)]) E) →
    0<lower.1.repr → lower.1.repr<eta.1.repr →
    ∃ (added : List (NONote × Nat)) (last : NONote),
      let result := encodedSuccessorNormalization (oneVariableComparisonEncode (.range w E))
        (rawNoteEncode eta.1) (rawNoteEncode lower.1) c
      result.1=oneVariableComparisonEncode (.range ((w++added)++[(last,c)]) E) ∧
      result.2.1=rawNoteEncode last.1 ∧
      oneVariableComparisonValid (.range ((w++added)++[(last,c)]) E) ∧
      lower.1.repr≤last.1.repr ∧ last.1.repr≤eta.1.repr ∧
      Vendor.R1.treeWeight last.1≤Vendor.R1.treeWeight eta.1 ∧
      (last.1.repr=lower.1.repr ∨ Order.IsSuccLimit last.1.repr) ∧
      (∀ p∈added,lower.1.repr<p.1.1.repr ∧ Vendor.R1.treeWeight p.1.1≤Vendor.R1.treeWeight eta.1) ∧
      1≤result.2.2 ∧
      ∀ x : Nat, result.2.2≤x →
        oneVariableComparisonDomainAt (.range (w++[(eta,c)]) E) x ∧
        oneVariableComparisonDomainAt (.range ((w++added)++[(last,c)]) E) x ∧
        actualPrincipalWordRun (comparisonRawWord (w++[(eta,c)])) (actualFixedLimitProfileEval E x)=
          actualPrincipalWordRun (comparisonRawWord ((w++added)++[(last,c)])) (actualFixedLimitProfileEval E x)

end LogicLineages.OrdinalComparison.Targets
