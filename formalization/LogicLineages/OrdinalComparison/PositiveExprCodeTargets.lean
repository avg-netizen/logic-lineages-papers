module
public import LogicLineages.OrdinalComparison.PositiveExprCodeDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

def PositiveExprCodeRoundTrip : Prop :=
  ∀ E : FixedLimitPositiveExpr, positiveExprDecode (positiveExprEncode E)=some E

def PositiveExprCodeInverse : Prop :=
  ∀ n : Nat, ∀ E : FixedLimitPositiveExpr, positiveExprDecode n=some E → positiveExprEncode E=n

def PositiveExprCodeDomain : Prop :=
  ∀ n : Nat, (positiveExprDecode n).isSome=true ↔ ∃ E : FixedLimitPositiveExpr, positiveExprEncode E=n

def PositiveExprMalformedRejected : Prop :=
  (∀ k : Nat, 0<k → positiveExprDecode (4*k+1)=none) ∧
    (∀ h a : Nat, rawNormalCode h≠1 → positiveExprDecode (4*Nat.pair h a+3)=none)

end LogicLineages.OrdinalComparison.Targets
