module
public import LogicLineages.OrdinalComparison.ComparisonSourceDomainDefinitions
public import Mathlib.Computability.Partrec

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

def ComparisonSourceDomainPrimitiveRecursive : Prop := Primrec encodedComparisonSourceDomain

def ComparisonSourceDomainCorrect : Prop :=
  ∀ E : OneVariableComparisonExpr, oneVariableComparisonValid E →
    encodedComparisonSourceDomain (oneVariableComparisonEncode E)=1

/-- ENTIRE numeric image of the literal P/R source grammar. Every accepted
raw input has a genuine source witness, including a nonempty typed kernel
word, positive normal exponents and an open actual P1 argument. No decoder,
source-validity or kernel-domain oracle is supplied. -/
def ComparisonSourceDomainImage : Prop :=
  ∀ n : Nat, encodedComparisonSourceDomain n=1 ↔
    ∃ E : OneVariableComparisonExpr, oneVariableComparisonEncode E=n ∧ oneVariableComparisonValid E

end LogicLineages.OrdinalComparison.Targets
