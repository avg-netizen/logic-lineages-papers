module
public import LogicLineages.OrdinalComparison.ProfileThresholdProgramDefinitions
public import Mathlib.Computability.Partrec

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

def ProfileSyntaxBudgetCalibration : Prop :=
  ∀ E : FixedLimitPositiveExpr,
    4≤fixedProfileSyntaxBudget E ∧ fixedLimitProfileThreshold E≤fixedProfileSyntaxBudget E ∧
    profileReserveBlocks (profileBoundWord E)≤fixedProfileSyntaxBudget E ∧
    profileReserveLeadingBound (profileBoundWord E)≤fixedProfileSyntaxBudget E ∧
    Vendor.R1.treeWeight (profilePrincipalDominator (profileBoundWord E)).1≤fixedProfileSyntaxBudget E

def ProfileSyntaxBudgetProgram : Prop :=
  Primrec encodedProfileSyntaxBudget ∧ ∀ E : FixedLimitPositiveExpr,
    encodedProfileSyntaxBudget (positiveExprEncode E)=fixedProfileSyntaxBudget E

def ActualProfileSupplierTailProgram : Prop :=
  Primrec₂ encodedProfileSupplierTail ∧ ∀ (L : NONote) (E : FixedLimitPositiveExpr),
    profileDirectThreshold L E≤encodedProfileSupplierTail (rawNoteEncode L.1) (positiveExprEncode E) ∧
    profileAdjacentThreshold L E≤encodedProfileSupplierTail (rawNoteEncode L.1) (positiveExprEncode E) ∧
    profileLimitMassThreshold L E≤encodedProfileSupplierTail (rawNoteEncode L.1) (positiveExprEncode E)

end LogicLineages.OrdinalComparison.Targets
