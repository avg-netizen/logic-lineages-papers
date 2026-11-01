module
public import LogicLineages.OrdinalComparison.SourceSignatureBudgetDefinitions
public import Mathlib.Computability.Partrec

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

def ActualSourceHeadNormBudget : Prop :=
  ∀ E : FixedLimitPositiveExpr, ∀ rho∈comparisonPositiveSourceHeads E,
    Vendor.R1.treeWeight rho.1≤fixedProfileSyntaxBudget E

def SourceSignatureBudgetProgram : Prop :=
  Primrec encodedSourceSignatureBudget ∧ Primrec₂ encodedPairSignatureBudget ∧
  ∀ E : OneVariableComparisonExpr, oneVariableComparisonValid E →
    encodedSourceSignatureBudget (oneVariableComparisonEncode E)=comparisonSourceSignatureBudget E ∧
    4≤comparisonSourceSignatureBudget E ∧
    (∀ rho∈comparisonOriginalSourceHeads E, Vendor.R1.treeWeight rho.1≤comparisonSourceSignatureBudget E) ∧
    (∀ p∈comparisonAuxiliarySourceWord E, Vendor.R1.treeWeight p.1.1≤comparisonSourceSignatureBudget E)

/-- An explicitly computed common finite ACTUAL carrier for every nested
original head's principal expansion and every initial auxiliary kernel on
both sides. Combined with successor closure this pays the finite source-Q
supplier. It does not assert the still-unpaid actual recursion/call graph. -/
def SourcePairSignatureCarrier : Prop :=
  ∀ E F : OneVariableComparisonExpr, oneVariableComparisonValid E → oneVariableComparisonValid F →
    let budget := encodedPairSignatureBudget (oneVariableComparisonEncode E) (oneVariableComparisonEncode F)
    ∀ G∈[E,F],
      (∀ rho∈comparisonOriginalSourceHeads G, ∀ eta∈principalExponentBlocks rho.1,
        rawNoteEncode eta∈encodedNormalNormBall budget) ∧
      (∀ p∈comparisonAuxiliarySourceWord G, rawNoteEncode p.1.1∈encodedNormalNormBall budget)

end LogicLineages.OrdinalComparison.Targets
