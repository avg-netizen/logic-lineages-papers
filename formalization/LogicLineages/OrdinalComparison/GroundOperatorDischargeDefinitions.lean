module
public import LogicLineages.OrdinalComparison.WWUnaryCarrierDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.GroundOperatorDischarge

/-- Discharge exactly the current ground binder by literal source zero.
Every old typed name keeps its identity; source substitution lifts under all
internal binders, including arbitrary higher types in opaque operators. -/
def groundMap (Γ : List Ty) : GroundClosing.GroundMap (.ground :: Γ) Γ
  | _, .here => .zero
  | _, .there x => .var x

def close {Γ : List Ty} {τ : Ty} (t : OriginalTerm (.ground :: Γ) τ) : OriginalTerm Γ τ :=
  t.substitute (GroundClosing.GroundMap.source (groundMap Γ))

/-- A witness records the actual entire source assignment, not only a freely
chosen positive expression. No claim here creates annotations in a scalar. -/
def OperatorWitness {Γ : List Ty} (p : AdmissibleSum.Policy) (h : OrdinalExpression Γ) : Prop :=
  ∃ (r : Nat) (t : OriginalTerm Γ (Ty.curriedGround (r+1)))
    (u : OrdinalVector Γ (Ty.curriedGround (r+1)).level),
    AdmissibleAssignment.assignment p t = some u ∧ u (UnaryCarrier.headIndex r) = h
end LogicLineages.OrdinalComparison.Source.GroundOperatorDischarge
