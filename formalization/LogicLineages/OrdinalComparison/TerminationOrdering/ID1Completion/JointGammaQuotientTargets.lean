module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaQuotientDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaQuotientTargets
open Source JointGammaQuotient

/-- Raw decoding is only an implementation representation; the original checker is unchanged. -/
def ActualRawEdgeCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Ty)
    (table : Fin n → Fin n → Bool) (x y certificate : Nat),
  rawEdgeTest n arity symbols S Gamma table x y certificate =
    NumberedNumericQuotientEdge.numericEdgeTest n arity symbols S Gamma table x y certificate

/-- The original numeric edge checker, with Gamma and every other datum variable. -/
def ActualJointEdgePrimitive : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat),
  Primrec (fun p : Parameters n × Nat × Nat × Nat =>
    NumberedNumericQuotientEdge.numericEdgeTest n arity
      p.1.1.1.1 p.1.1.1.2 p.1.1.2 p.1.2 p.2.1 p.2.2.1 p.2.2.2)

/-- The original ordered path checker including its exact empty-path endpoint test. -/
def ActualJointPathPrimitive : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat),
  Primrec (fun p : Parameters n × Nat × Nat × List NumberedQuotientPathCertificates.EdgeEntry =>
    NumberedQuotientPathCertificates.pathTest n arity
      p.1.1.1.1 p.1.1.1.2 p.1.1.2 p.1.2 p.2.1 p.2.2.1 p.2.2.2)

/-- The original positive-path checker on its original numeric certificate codes.
Malformed and empty certificates are still rejected, including at equal endpoints. -/
def ActualJointPositivePrimitive : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat),
  Primrec (fun p : Parameters n × Nat × Nat × Nat =>
    NumberedQuotientPathCertificates.positivePathTest n arity
      p.1.1.1.1 p.1.1.1.2 p.1.1.2 p.1.2 p.2.1 p.2.2.1 p.2.2.2)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaQuotientTargets
