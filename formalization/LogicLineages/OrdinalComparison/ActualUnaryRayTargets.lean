module
public import LogicLineages.OrdinalComparison.ActualUnaryRayDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ActualUnaryRay.Targets
open ForwardTranslation OriginalDomain

def GenuineRayAndComputability : Prop := ∀ (a : ClosedPositive) (c : Nat),
  Computable (rayValue a c) ∧
  ∀ n : Nat, actualOrdinalNorm (fixedHead a) ≤ totalNorm a c n ∧
    rayValue a c n = actualCollapse (fixedHead a + ((c+1+n : Nat) : Ordinal))

/-- All original unary sources, unrestricted internally. The whole actual
application vector and exact K constants are constructed, not supplied. -/
def ActualSourceRay : Prop := ∀ (Γ : List Ty) (K : OriginalTerm Γ (Ty.curriedGround 1)),
  ∃ (u : OrdinalVector Γ (Ty.curriedGround 1).level) (a : ClosedPositive) (c : Nat)
      (v : OrdinalVector (.ground :: Γ) Ty.ground.level),
    Constants K u a c ∧
    AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy (source K) = some v ∧
    (∀ μ : Variable Γ .ground → Nat,
      expressionValue (UnitObservation.substitution μ) (u (UnaryCarrier.headIndex 0)) = a.evaluate.1.repr) ∧
    (∀ μ : Variable Γ .ground → Nat,
      expressionValue (UnitObservation.substitution μ)
        ((GroundClosing.vector (UnaryCarrier.groundMap Γ) u) 0) = (c : Ordinal)) ∧
    ∀ ρ : Variable (.ground :: Γ) .ground → Nat,
      expressionValue (UnitObservation.substitution ρ) (v 0) = (rayValue a c (ρ .here) : Ordinal)

/-- Exact observation by the existing literal unit-elimination tree; all its
source atoms really have ground-only free contexts. No graph oracle is used. -/
def ActualRayObservation : Prop := ∀ (Γ : List Ty) (K : OriginalTerm Γ (Ty.curriedGround 1)),
  ∃ (u : OrdinalVector Γ (Ty.curriedGround 1).level) (a : ClosedPositive) (c : Nat)
      (q : UnitElimination.Tree (Nat×Nat) (.ground :: Γ)),
    Constants K u a c ∧
    UnitElimination.build ((.ground :: Γ).length+1) (source K) = some q ∧
    (∀ s ∈ UnitElimination.sources (UnitElimination.realize q), ∀ σ ∈ s.1, σ = Ty.ground) ∧
    ∀ (ρ : Variable (.ground :: Γ) .ground → Nat) (r : Nat),
      UnitElimination.Eval (UnitElimination.realize q) ρ r ↔ r = rayValue a c (ρ .here)
end LogicLineages.OrdinalComparison.Source.ActualUnaryRay.Targets
