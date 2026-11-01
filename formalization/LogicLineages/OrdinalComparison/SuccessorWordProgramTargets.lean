module
public import LogicLineages.OrdinalComparison.SuccessorWordProgramDefinitions
public import Mathlib.Computability.Partrec

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

def SuccessorWordProgramsPrimitiveRecursive : Prop :=
  Primrec (fun p : Nat × Nat × Nat => encodedComparisonAppendKernel p.1 p.2.1 p.2.2) ∧
  Primrec (fun p : Nat × Nat × Nat × Nat => encodedSuccessorWordExpansion p.1 p.2.1 p.2.2.1 p.2.2.2) ∧
  Primrec (fun p : Nat × Nat × Nat × Nat => encodedSuccessorWordTail p.1 p.2.1 p.2.2.1 p.2.2.2)

def SuccessorWordProgramsSource : Prop :=
  ∀ (w : List (NONote × Nat)) (E : FixedLimitPositiveExpr) (eta pred : NONote) (c : Nat),
    encodedComparisonAppendKernel (oneVariableComparisonEncode (.range w E)) (rawNoteEncode eta.1) c=
      oneVariableComparisonEncode (.range (w++[(eta,c)]) E) ∧
    encodedSuccessorWordExpansion (oneVariableComparisonEncode (.range w E))
        (rawNoteEncode eta.1) (rawNoteEncode pred.1) c=
      oneVariableComparisonEncode (.range (successorExpandedWord w eta pred c) E)

/-- Literal source successor expansion, with EVERY count retained. Both
words' dynamic genuine domains are consequences of the computed code tail.
The supplied exponent successor equation is the source branch condition,
not an unproved expansion/termination/semantic oracle. -/
def ActualSuccessorWordProgram : Prop :=
  SuccessorWordProgramsPrimitiveRecursive ∧
  ∀ (w : List (NONote × Nat)) (E : FixedLimitPositiveExpr) (eta pred : NONote) (c : Nat),
    oneVariableComparisonValid (.range (w++[(eta,c)]) E) → 0<pred.1.repr →
    eta.1.repr=pred.1.repr+1 →
    oneVariableComparisonValid (.range (successorExpandedWord w eta pred c) E) ∧
    ∀ x : Nat,
      encodedSuccessorWordTail (oneVariableComparisonEncode (.range w E))
        (rawNoteEncode eta.1) (rawNoteEncode pred.1) c≤x →
      oneVariableComparisonDomainAt (.range (w++[(eta,c)]) E) x ∧
      oneVariableComparisonDomainAt (.range (successorExpandedWord w eta pred c) E) x ∧
      actualPrincipalWordRun (comparisonRawWord (w++[(eta,c)])) (actualFixedLimitProfileEval E x)=
        actualPrincipalWordRun (comparisonRawWord (successorExpandedWord w eta pred c))
          (actualFixedLimitProfileEval E x)

end LogicLineages.OrdinalComparison.Targets
