module
public import LogicLineages.OrdinalComparison.ComparisonSignatureDefinitions
public import LogicLineages.OrdinalComparison.ProfileThresholdProgramDefinitions
public import LogicLineages.OrdinalComparison.OneVariableComparisonDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison

def comparisonPositiveSourceHeads : FixedLimitPositiveExpr → List NONote
  | .constant _ => []
  | .input => []
  | .add E F => comparisonPositiveSourceHeads E++comparisonPositiveSourceHeads F
  | .head rho E => rho::comparisonPositiveSourceHeads E

def comparisonOriginalSourceHeads : OneVariableComparisonExpr → List NONote
  | .positive E | .range _ E => comparisonPositiveSourceHeads E

def comparisonAuxiliarySourceWord : OneVariableComparisonExpr → List (NONote × Nat)
  | .positive _ => []
  | .range w _ => w

/-- A fixed whole-source budget dominates every original nested head and
initial auxiliary exponent. Future successor normalization only lowers norms. -/
def comparisonSourceSignatureBudget : OneVariableComparisonExpr → Nat
  | .positive E => fixedProfileSyntaxBudget E
  | .range w E => max (fixedProfileSyntaxBudget E) (comparisonWordDomainBound w)

def encodedSourceSignatureBudget (n : Nat) : Nat :=
  if n%2=0 then encodedProfileSyntaxBudget (n/2)
  else max (encodedProfileSyntaxBudget (n/2).unpair.2) (encodedOneVariableComparisonDomainBound n)

def encodedPairSignatureBudget (n m : Nat) : Nat :=
  max (encodedSourceSignatureBudget n) (encodedSourceSignatureBudget m)

end LogicLineages.OrdinalComparison
