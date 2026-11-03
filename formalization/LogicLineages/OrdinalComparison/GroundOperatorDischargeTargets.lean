module
public import LogicLineages.OrdinalComparison.GroundOperatorDischargeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.GroundOperatorDischarge.Targets

def ExactHeadClosure : Prop := ∀ (Γ : List Ty) (e : OrdinalExpression (.ground :: Γ)),
  GroundClosing.expression (groundMap Γ) e = ordinalHeadClosure e

/-- Equality of actual optional whole vectors for every policy and source
result type. Zero is an actual source constant, not a substituted scalar one. -/
def WholeAssignment : Prop := ∀ (Γ : List Ty) (τ : Ty) (p : AdmissibleSum.Policy)
    (t : OriginalTerm (.ground :: Γ) τ),
  AdmissibleAssignment.assignment p (close t) =
    (AdmissibleAssignment.assignment p t).map (fun u j => ordinalHeadClosure (u j))

/-- Both actual source assignments exist unconditionally. The entire vector,
including the original scalar, is transported; no synthetic scalar reset. -/
def ActualFunctionalDischarge : Prop := ∀ (Γ : List Ty) (r : Nat) (p : AdmissibleSum.Policy)
    (t : OriginalTerm (.ground :: Γ) (Ty.curriedGround (r+1))),
  ∃ (u : OrdinalVector (.ground :: Γ) (Ty.curriedGround (r+1)).level)
    (v : OrdinalVector Γ (Ty.curriedGround (r+1)).level),
    AdmissibleAssignment.assignment p t = some u ∧
    AdmissibleAssignment.assignment p (close t) = some v ∧
    (∀ j, v j = ordinalHeadClosure (u j)) ∧
    v 0 = ordinalHeadClosure (u 0) ∧
    v (UnaryCarrier.headIndex r) = ordinalHeadClosure (u (UnaryCarrier.headIndex r))

/-- Transport an explicit actual source witness, never assume that arbitrary
heads have operators. The output witness is the literal closed input source. -/
def OperatorWitnessTransport : Prop := ∀ (Γ : List Ty) (p : AdmissibleSum.Policy)
    (h : OrdinalExpression (.ground :: Γ)),
  OperatorWitness p h → OperatorWitness p (ordinalHeadClosure h)
end LogicLineages.OrdinalComparison.Source.GroundOperatorDischarge.Targets
