module
public import LogicLineages.OrdinalComparison.OriginalGroundDataConstructionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.OriginalGroundDataConstruction.Targets
open DeterministicAccountData ScalarCarrierAccounting OriginalDomain OriginalScaleFlatList
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

def ExactPackaging : Prop := ∀ (k : Nat) (Γ : List Ty)
    (rs : List (UnaryRecord (Ty.curriedGround (k+1) :: Ty.curriedGround (k+1) :: Γ)))
    (ha : ∀ r ∈ rs, r.Assigned),
  (operators rs ha).length = rs.length ∧
  (operators rs ha).map (fun op => unitValue (op.vector 1)) = rs.map (fun r => unitValue (r.vector 1))

def ActualPaidAccount : Prop := ∀ (k : Nat) (Γ : List Ty)
    (P : TrackedSource.Expr k (Ty.curriedGround (k+1) :: Γ) .here 0),
  TrackedSource.active P = true →
  ∃ u rs c labels, sourceAccount P = some (u,rs,c) ∧
    AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy (TrackedSource.erase P) = some u ∧
    List.Forall₂ Matches rs labels ∧ Account (u 0) labels c ∧ 3*rs.length+4 ≤ c

/-- Semantic/data-level original-budget construction, retaining the actual
original B and caller vectors. Numeric computability of the whole typed/raw
source transformation remains a separate obligation. -/
def ActualOriginalGroundConstruction : Prop := ∀ (k : Nat) (Γ : List Ty)
    (P : TrackedSource.Expr k (Ty.curriedGround (k+1) :: Γ) .here 0)
    (C : OriginalTerm Γ (Ty.curriedGround (k+1))), TrackedSource.active P = true →
  ∃ (u : OrdinalVector (Ty.curriedGround (k+1) :: Γ) 0)
    (B : OrdinalVector Γ (Ty.arrow (Ty.curriedGround (k+1)) Ty.ground).level)
    (caller : OrdinalVector Γ (Ty.curriedGround (k+1)).level) (b : Nat)
    (rs : List (UnaryRecord (Ty.curriedGround (k+1) :: Ty.curriedGround (k+1) :: Γ)))
    (c : Nat) (hr : ∀ r ∈ rs, r.Assigned),
    sourceAccount P = some (u,rs,c) ∧
    AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy (TrackedSource.erase P) = some u ∧
    AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy (.lam (TrackedSource.erase P)) = some B ∧
    AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy C = some caller ∧
    b = OriginalSecondBudget.scalarSecond (u 0) ∧ 4 ≤ b ∧ 3*rs.length+4 ≤ c ∧
    AdmissibleAssignment.box OrdinalSyntax.defaultPolicy B caller (OriginalSecondBudget.boxSecond k) =
      B (OriginalSecondBudget.boxSecond k) ∧
    (∀ ν : OrdinalComponent Γ → Ordinal, denote ν (B (OriginalSecondBudget.boxSecond k)) = (b : Ordinal)) ∧
    ∃ (vC : OrdinalVector Γ 1)
      (hSat : AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy (UnaryCarrier.saturate k C) = some vC),
      (∀ ν : OrdinalComponent Γ → Ordinal, denote ν (vC 1) = denote ν (caller (UnaryCarrier.headIndex k))) ∧
      let inputs := paidList b (operators rs hr) (unaryInput Γ (UnaryCarrier.saturate k C) vC hSat)
      ∃ K : OrdinalVector (HeterogeneousUnaryAssembly.context inputs) 1,
        AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy
          (SourceUnaryChain.chainSource (HeterogeneousUnaryAssembly.terms inputs)) = some K ∧
        0 < gap b (operators rs hr) c ∧
        ∀ (ρ : Variable Γ .ground → Nat)
          (μ : Variable (HeterogeneousUnaryAssembly.context inputs) .ground → Nat),
          ordinalNaturalProduct (scale b : Ordinal)
            (ordinalNaturalSum (expressionValue (UnitObservation.substitution ρ) (B (boxFirst k)))
              (expressionValue (UnitObservation.substitution ρ) (caller (UnaryCarrier.headIndex k)))) =
            expressionValue (UnitObservation.substitution μ) (K 1) + (gap b (operators rs hr) c : Ordinal)
end LogicLineages.OrdinalComparison.Source.OriginalGroundDataConstruction.Targets
