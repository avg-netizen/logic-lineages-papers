module
public import LogicLineages.OrdinalComparison.OriginalHeadWireCodeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ActualHeadGraph.OriginalHeadWireCode.Targets
open Arithmetic ArithmeticCode OriginalDomain
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

def ActualScalarFiniteness : Prop := ∀ (Γ : List Ty) (τ : Ty) (t : OriginalTerm Γ τ),
  ∃ u : OrdinalVector Γ τ.level,
    AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy t = some u ∧
    ∀ ρ : Variable Γ .ground → Nat,
      expressionValue (UnitObservation.substitution ρ) (u 0) = (scalarValue u ρ : Ordinal)

def EffectiveCompiler : Prop := Computable (fun p : RawInput =>
  compileCode p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1 p.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2)

/-- Complete original-wire consumer of the printed paid certificate. The
finite budget is exactly the original untruncated full box's coordinate two;
no lower bound on b or positive-gap strengthening is added. -/
def ActualOriginalWire : Prop := ∀ (Γ Θ : List Ty) (σ τ : Ty) (hσ : 0<σ.level)
    (B : OriginalTerm Γ (Ty.arrow σ τ)) (C : OriginalTerm Γ σ)
    (K : OriginalTerm Θ (Ty.curriedGround 1)),
  ∃ (uB : OrdinalVector Γ (Ty.arrow σ τ).level) (uC : OrdinalVector Γ σ.level)
      (uK : OrdinalVector Θ (Ty.curriedGround 1).level),
    AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy B = some uB ∧
    AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy C = some uC ∧
    AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy K = some uK ∧
    (∀ ρ : Variable Γ .ground → Nat,
      expressionValue (UnitObservation.substitution ρ) (uB 0) = (scalarValue uB ρ : Ordinal) ∧
      expressionValue (UnitObservation.substitution ρ) (uC 0) = (scalarValue uC ρ : Ordinal)) ∧
    ∀ (b δ : Nat),
      denote (fun _ => 1) (AdmissibleAssignment.box OrdinalSyntax.defaultPolicy uB uC (boxSecond σ τ hσ)) = (b : Ordinal) →
      originalPaidValue σ τ hσ b uB uC =
        expressionValue (UnitObservation.substitution (fun _ => 0)) (uK (UnaryCarrier.headIndex 0)) + (δ : Ordinal) →
      ∀ (xs : List Expr) (y : Expr), Γ.length ≤ xs.length →
        ∃ f : Formula,
          compileCode (Γ.map SyntaxCode.typeCode) (SyntaxCode.encodeTerm B) (SyntaxCode.encodeTerm C)
            (Θ.map SyntaxCode.typeCode) (SyntaxCode.encodeTerm K) δ (xs.map exprCode) (exprCode y) = some (formulaCode f) ∧
          ∀ ν : Nat → Nat,
            let ξ := PaidHeadTransport.paidHead (originalPaidValue σ τ hσ b uB uC)
            let t := originalWire ξ σ.level uB uC (inputValues ν xs)
            actualOrdinalNorm ξ ≤ t ∧ (f.eval ν ↔ y.value ν = actualHeadValue ξ t)
end LogicLineages.OrdinalComparison.Source.ActualHeadGraph.OriginalHeadWireCode.Targets
