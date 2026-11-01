module
public import LogicLineages.OrdinalComparison.AffineProfileCertificateDefinitions
public import LogicLineages.OrdinalComparison.OneVariableComparisonDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison

def encodedKernelProfileLeafTail (L P c : Nat) : Nat :=
  max (encodedProfileSupplierTail L P) (c+rawNormCode L)

def oneVariableComparisonOpen : OneVariableComparisonExpr → Prop
  | .positive E => positiveExprHasInput E=true
  | .range _ _ => True

end LogicLineages.OrdinalComparison
