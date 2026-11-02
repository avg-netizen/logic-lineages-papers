module
public import LogicLineages.OrdinalComparison.OriginalScaleFlatListDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.OriginalScaleFlatList.Targets
open HeterogeneousUnaryAssembly ScalarCarrierAccounting OriginalDomain
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

def LiteralReplication : Prop := ∀ (Γ : List Ty) (b : Nat) (xs : List (Operator Γ)) (caller : Operator Γ),
  (paidList b xs caller).length = scale b * xs.length + scale b ∧
  (paidList b xs caller).map (fun op => unitValue (op.vector 1)) =
    (List.replicate (scale b) (xs.map (fun op => unitValue (op.vector 1)))).flatten ++
      List.replicate (scale b) (unitValue (caller.vector 1))

def ExactPositiveGap : Prop := ∀ (Γ : List Ty) (b : Nat) (xs : List (Operator Γ)) (c : Nat),
  4 ≤ b → 3*xs.length+4 ≤ c →
    0 < gap b xs c ∧ gap b xs c + 1 = scale b * (c - 3*xs.length - 3)

/-- Given actual carrier records and a paid finite reserve, derive the actual
original caller assignment and saturation, then build ONE actual chain on the
literal original-scale flat list. This does not extract the list from P. -/
def ActualOriginalScaleChain : Prop := ∀ (k : Nat) (Γ : List Ty)
    (xs : List (Operator Γ)) (C : OriginalTerm Γ (Ty.curriedGround (k+1))) (b c : Nat),
  4 ≤ b → 3*xs.length+4 ≤ c →
  ∃ (uC : OrdinalVector Γ (Ty.curriedGround (k+1)).level) (vC : OrdinalVector Γ 1)
    (hC : AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy C = some uC)
    (hSat : AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy (UnaryCarrier.saturate k C) = some vC),
    (∀ ν : OrdinalComponent Γ → Ordinal, denote ν (vC 1) = denote ν (uC (UnaryCarrier.headIndex k))) ∧
    let inputs := paidList b xs (unaryInput Γ (UnaryCarrier.saturate k C) vC hSat)
    ∃ K : OrdinalVector (HeterogeneousUnaryAssembly.context inputs) 1,
      AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy
        (SourceUnaryChain.chainSource (HeterogeneousUnaryAssembly.terms inputs)) = some K ∧
      0 < gap b xs c ∧
      ∀ (ρ : Variable Γ .ground → Nat)
        (μ : Variable (HeterogeneousUnaryAssembly.context inputs) .ground → Nat),
        ordinalNaturalProduct (scale b : Ordinal)
          (ordinalNaturalSum (sourceSum xs + (c : Ordinal))
            (expressionValue (UnitObservation.substitution ρ) (uC (UnaryCarrier.headIndex k)))) =
          expressionValue (UnitObservation.substitution μ) (K 1) + (gap b xs c : Ordinal)
end LogicLineages.OrdinalComparison.Source.OriginalScaleFlatList.Targets
