module
public import LogicLineages.OrdinalComparison.HeadFiniteSurplusDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.HeadFiniteSurplus.Targets
open AdditiveHeadTree OriginalDomain
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

/-- Actual success is derived from the head tree; the finite surplus is added
by ordinary ordinal addition, exactly as in the source displayed equation.
The remaining valuation is arbitrary, stronger than common-unit observation. -/
def ExactHeadPartial : Prop := ∀ (k : Nat) (Γ : List Ty) (p : AdmissibleSum.Policy)
    (h : OrdinalExpression (Ty.curriedGround (k+1) :: Γ)),
  HeadTree (.here : Variable (Ty.curriedGround (k+1) :: Γ) (Ty.curriedGround (k+1))) h →
  ∃ v : OrdinalPartialVector Γ (Ty.curriedGround (k+1)),
    AdmissiblePartial.run p 1 h = some v ∧
    ∀ ν : OrdinalComponent Γ → Ordinal,
      denote ν (v (outputOne k)) = denote ν (ordinalHeadClosure h) + (surplus h : Ordinal) ∧
      denote ν (v (outputTwo k)) = (secondCount h : Ordinal)

def SurplusBounds : Prop := ∀ (k : Nat) (Γ : List Ty)
    (h : OrdinalExpression (Ty.curriedGround (k+1) :: Γ)),
  HeadTree (.here : Variable (Ty.curriedGround (k+1) :: Γ) (Ty.curriedGround (k+1))) h →
    0 < secondCount h ∧
    (surplus h = 0 ↔ h = .var ⟨_,.here,UnaryCarrier.headIndex k⟩) ∧
    ∀ ν : OrdinalComponent Γ → Ordinal,
      Ordinal.omega0 ≤ denote ν (ordinalHeadClosure h) → 1 ≤ surplus h

/-- Unconditional actual functional-source instantiation, all structural
policies, all old/new ground observations, the same common functional units.
Neither an assignment, head decomposition nor partial success is a premise. -/
def ActualSourceSurplus : Prop := ∀ (k : Nat) (Γ : List Ty) (r : Nat)
    (p : AdmissibleSum.Policy)
    (e : TrackedSource.Expr k (Ty.curriedGround (k+1) :: Γ) .here (r+1)),
  ∃ (u : OrdinalVector (Ty.curriedGround (k+1) :: Γ) (Ty.curriedGround (r+1)).level)
    (v : OrdinalPartialVector Γ (Ty.curriedGround (k+1))),
    AdmissibleAssignment.assignment p (TrackedSource.erase e) = some u ∧
    AdmissiblePartial.run p 1 (u (UnaryCarrier.headIndex r)) = some v ∧
    0 < secondCount (u (UnaryCarrier.headIndex r)) ∧
    (surplus (u (UnaryCarrier.headIndex r)) = 0 ↔
      u (UnaryCarrier.headIndex r) = .var ⟨_,.here,UnaryCarrier.headIndex k⟩) ∧
    ∀ (ρ : Variable (Ty.curriedGround (k+1) :: Γ) .ground → Nat)
      (μ : Variable Γ .ground → Nat),
      expressionValue (UnitObservation.substitution μ) (v (outputOne k)) =
        expressionValue (UnitObservation.substitution ρ) (u (UnaryCarrier.headIndex r)) +
          (surplus (u (UnaryCarrier.headIndex r)) : Ordinal) ∧
      expressionValue (UnitObservation.substitution μ) (v (outputTwo k)) =
        (secondCount (u (UnaryCarrier.headIndex r)) : Ordinal) ∧
      (Ordinal.omega0 ≤ expressionValue (UnitObservation.substitution ρ) (u (UnaryCarrier.headIndex r)) →
        1 ≤ surplus (u (UnaryCarrier.headIndex r)))
end LogicLineages.OrdinalComparison.Source.HeadFiniteSurplus.Targets
