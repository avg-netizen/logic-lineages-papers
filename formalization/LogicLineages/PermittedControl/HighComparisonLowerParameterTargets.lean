module
public import LogicLineages.PermittedControl.RawFieldComparisonFormTargets
public import LogicLineages.PermittedControl.ClosedOrdinaryFieldTargets

@[expose] public section
namespace LogicLineages.PermittedControl.HighComparisonLowerParameter
open OrdinalComparison FieldComparison

/-- When the original comparison yields an entry parameter, its upper
endpoint is literally that of the field at the smaller raw argument.
Only the original source lower-endpoint advance and iterate may change. -/
def SmallerEntryHeadExact : Prop :=
  ∀ (F G : ValueField) (sign a : Nat) (lam mu : NONote),
    distinctForm F G = .linear sign (.entry a lam mu) →
      ∃ (outer : Nat) (originalLower : NONote), F = .entry outer lam originalLower

def AffordableLowerParameter : Prop :=
  ∀ (B : Nat) (F G H : ValueField) (sign x : Nat),
    distinctForm F G = .linear sign H → ProperField H →
      longFieldDistinctBound B F G ≤ x → ClosedOrdinaryValueDomain H x

def OriginalFieldCodeExact : Prop :=
  Function.Injective longFieldCode ∧
  ∀ (sign sign' : Nat) (H H' : ValueField),
    rawLinearForm sign (longFieldCode H) = rawLinearForm sign' (longFieldCode H') →
      sign = sign' ∧ H = H'

def FullHighComparisonLowerParameter : Prop :=
  SmallerEntryHeadExact ∧ AffordableLowerParameter ∧ OriginalFieldCodeExact

end LogicLineages.PermittedControl.HighComparisonLowerParameter
