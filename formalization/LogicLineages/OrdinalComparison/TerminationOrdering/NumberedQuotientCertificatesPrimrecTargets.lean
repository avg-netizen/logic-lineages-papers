module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedQuotientPathCertificatesDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRepresentativePrimrecProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedStepCodecPrimrecProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedQuotientCertificatesPrimrecTargets
open Source NumberedNumericQuotientEdge NumberedQuotientPathCertificates

/-- The original quotient-edge checker retains the actual source/target representative tests. -/
def ActualNumericEdgePrimitive : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty),
    Primrec (fun p : (List (Fin n) × List Ty) × (Fin n → Fin n → Bool) × Nat × Nat × Nat =>
      numericEdgeTest n arity p.1.1 p.1.2 Gamma p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)

def ActualPathCertificateDecoderPrimitive : Prop := Primrec decodePathCertificate

/-- Every literal edge entry is checked in its original order, ending at the requested vertex. -/
def ActualPathTestPrimitive : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty),
    Primrec (fun p : (List (Fin n) × List Ty) × (Fin n → Fin n → Bool) ×
        Nat × Nat × List EdgeEntry =>
      pathTest n arity p.1.1 p.1.2 Gamma p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)

/-- The original positive-path checker rejects an empty certificate, even at equal endpoints. -/
def ActualPositivePathTestPrimitive : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty),
    Primrec (fun p : (List (Fin n) × List Ty) × (Fin n → Fin n → Bool) × Nat × Nat × Nat =>
      positivePathTest n arity p.1.1 p.1.2 Gamma p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedQuotientCertificatesPrimrecTargets
