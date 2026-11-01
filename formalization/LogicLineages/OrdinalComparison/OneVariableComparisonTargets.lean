module
public import LogicLineages.OrdinalComparison.OneVariableComparisonDefinitions
public import Mathlib.Computability.Partrec

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

/-- Source section8's open-input supplier, paid for the literal P1 grammar. -/
def ActualOneVariableOpenInputLowerBound : Prop :=
  ∀ E : FixedLimitPositiveExpr, fixedLimitProfileBelow epsilonZero E → positiveExprHasInput E=true →
    ∀ x : Nat, x≤actualFixedLimitProfileEval E x

def ActualSuffixKernelInputExpansive : Prop :=
  ∀ (pi : Ordinal.{0}) (c t : Nat), t≤actualSuffixKernel pi c t

/-- Every dynamic domain along an arbitrary actual finite kernel word is
DERIVED from its fixed syntax bound. No word-action/domains oracle remains. -/
def ActualComparisonWordDomains : Prop :=
  ∀ (w : List (NONote × Nat)) (t : Nat), comparisonWordDomainBound w≤t →
    actualPrincipalWordGenuine (comparisonRawWord w) t ∧
      t≤(actualPrincipalWordRun (comparisonRawWord w) t).1

/-- Whole literal section8 syntax/evaluation/domain bridge, not the still
unpaid eventual comparison/separation algorithm. Covers both actual sorts,
uniform all-code evaluation and a primitive recursive genuine-domain bound. -/
def OneVariableComparisonSourceProgram : Prop :=
  Primrec encodedOneVariableComparisonDomainBound ∧
  Computable₂ encodedOneVariableComparisonValue ∧
  ∀ E : OneVariableComparisonExpr, oneVariableComparisonValid E →
    encodedOneVariableComparisonDomainBound (oneVariableComparisonEncode E)=
      oneVariableComparisonDomainBound E ∧
    1≤oneVariableComparisonDomainBound E ∧
    ∀ x : Nat, oneVariableComparisonDomainBound E≤x →
      oneVariableComparisonDomainAt E x ∧
      encodedOneVariableComparisonValue (oneVariableComparisonEncode E) x=
        actualOneVariableComparisonValue E x

end LogicLineages.OrdinalComparison.Targets
