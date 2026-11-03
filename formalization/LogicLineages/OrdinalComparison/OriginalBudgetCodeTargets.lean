module
public import LogicLineages.OrdinalComparison.OriginalBudgetCodeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.OriginalBudgetCode.Targets
open OriginalSecondBudget
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

def ExactCounts : Prop := ∀ (Γ : List Ty) (σ : Ty) (q : OrdinalExpression (σ::Γ)),
  countData (OrdinalSyntax.typedCode q) =
    (ordinalHeadFree q,HeadFiniteSurplus.secondCount q,scalarSecond q)

def PrimitiveRecursiveAlgorithms : Prop := Primrec countData ∧ Primrec secondCode ∧ Primrec₂ budgetCode

/-- The budget extracted from the actual original raw body is the untruncated
coordinate two of the original abstraction/full box for every actual caller. -/
def ActualOriginalBoxBudget : Prop := ∀ (k : Nat) (Γ : List Ty)
    (P : TrackedSource.Expr k (Ty.curriedGround (k+1)::Γ) .here 0)
    (C : OriginalTerm Γ (Ty.curriedGround (k+1))), TrackedSource.active P = true →
  ∃ (u : OrdinalVector (Ty.curriedGround (k+1)::Γ) 0)
    (B : OrdinalVector Γ (Ty.arrow (Ty.curriedGround (k+1)) Ty.ground).level)
    (caller : OrdinalVector Γ (Ty.curriedGround (k+1)).level) (b : Nat),
    AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy (TrackedSource.erase P) = some u ∧
    AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy (.lam (TrackedSource.erase P)) = some B ∧
    AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy C = some caller ∧
    budgetCode ((Ty.curriedGround (k+1)::Γ).map SyntaxCode.typeCode)
      (SyntaxCode.encodeTerm (TrackedSource.erase P)) = some b ∧
    b = scalarSecond (u 0) ∧ 4 ≤ b ∧
    AdmissibleAssignment.box OrdinalSyntax.defaultPolicy B caller (boxSecond k) = B (boxSecond k) ∧
    ∀ ν : OrdinalComponent Γ → Ordinal,
      denote ν (B (boxSecond k)) = (b : Ordinal)
end LogicLineages.OrdinalComparison.Source.OriginalBudgetCode.Targets
