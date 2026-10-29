module

public import LogicLineages.ComputabilityKnowledge.FiniteDepthEnvelope
public import LogicLineages.OrdinalComparison.ControlDefinitions

@[expose] public section

/-! Exact cross-lane composition at paper02 lines257–283. The numerical
hierarchy is the existing literal F₀(n)=2^n, Fⱼ₊₁(n)=Fⱼ^[n+1](n).
The affine term is the existing g=5(L+1)(1+sum distinct variables), with
unchanged shared valuation and finite-variable domain. No ψ/C-vector claim. -/
namespace LogicLineages.ComputabilityKnowledge.Comparators.FiniteDepthControl
open PositiveExpression CircuitReduction FiniteDepthEnvelope

def Target : Prop :=
  ∀ (e : Expr Nat), e.depth ≤ 2 →
    (envelope e).depth = 0 ∧
    (∀ d : Nat, Bounded d (envelope e) ↔ Bounded d e) ∧
    ∀ ρ : Nat → PosNat, 0 < (envelope e).eval ρ ∧
      e.eval ρ ≤ LogicLineages.OrdinalComparison.fastControl 2 ((envelope e).eval ρ)

end LogicLineages.ComputabilityKnowledge.Comparators.FiniteDepthControl
