module
public import LogicLineages.OrdinalComparison.PaidHeadTransportDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ActualHeadGraph.PaidHeadTransport.Targets
open Arithmetic ArithmeticCode OriginalDomain

def ExactOmegaFiniteTail : Prop := ∀ (a : Ordinal), a < epsilonZero → ∀ δ : Nat,
  ordinalNaturalProduct Ordinal.omega0 (a+(δ : Ordinal)) =
    ordinalNaturalProduct Ordinal.omega0 a + Ordinal.omega0*(δ : Ordinal)

/-- Actual K supplies its whole assigned vector. The explicit paid-certificate
premise is the paper's premise, and the exact already-computable compiler is
independent of its proof. No original B/C scalar wire is inserted here. -/
def ActualPaidGraph : Prop := ∀ (Γ : List Ty) (K : OriginalTerm Γ (Ty.curriedGround 1)),
  ∃ u : OrdinalVector Γ (Ty.curriedGround 1).level,
    AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy K = some u ∧
    ∀ (δ : Nat) (a : Ordinal) (μ : Variable Γ .ground → Nat),
      a = expressionValue (UnitObservation.substitution μ) (u (UnaryCarrier.headIndex 0)) + (δ : Ordinal) →
      ∀ (t y : Expr), ∃ f : Formula,
        GraphCode.compileCode (Γ.map SyntaxCode.typeCode) (SyntaxCode.encodeTerm K) δ (exprCode t) (exprCode y) =
          some (formulaCode f) ∧
        ∀ ν : Nat → Nat, f.eval ν ↔
          actualOrdinalNorm (paidHead a) ≤ t.value ν ∧ y.value ν = actualHeadValue (paidHead a) (t.value ν)
end LogicLineages.OrdinalComparison.Source.ActualHeadGraph.PaidHeadTransport.Targets
