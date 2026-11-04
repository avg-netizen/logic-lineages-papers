module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMulPrimrecDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMultisetPresentationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMulPrimrecTargets
open Source NumberedRewriteReduction NumberedAuxiliaryCoding NumberedMultisetCertificate
open NumberedMulCertificate NumberedNumericMul NumberedMulPrimrec

/-- Exact equality with the original typed Mul test on every actual packed input. -/
def ActualMulCodeCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Ty)
    (q r : Packed (Fin n) arity Gamma) (certificate : MultisetCertificate n arity Gamma),
    codeMulTest n arity symbols S Gamma (termCode q.2) (termCode r.2) certificate =
      mulCertificateTest n arity symbols S Gamma q r certificate

/-- Primitive recursion of the structural computation on arbitrary raw code pairs. -/
def ActualMulCodePrimitive : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty),
    Primrec (fun p : (List (Fin n) × List Ty) ×
        Code (Fin n) × Code (Fin n) × MultisetCertificate n arity Gamma =>
      codeMulTest n arity p.1.1 p.1.2 Gamma p.2.1 p.2.2.1 p.2.2.2)

/-- The original Mul certificate decision, jointly in windows, endpoints, and certificate. -/
def ActualMulCertificatePrimitive : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty),
    Primrec (fun p : (List (Fin n) × List Ty) ×
        Packed (Fin n) arity Gamma × Packed (Fin n) arity Gamma ×
          MultisetCertificate n arity Gamma =>
      mulCertificateTest n arity p.1.1 p.1.2 Gamma p.2.1 p.2.2.1 p.2.2.2)

/-- The original numeric decision on every natural endpoint and certificate code. -/
def ActualNumericMulPrimitive : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty),
    Primrec (fun p : (List (Fin n) × List Ty) × Nat × Nat × Nat =>
      numericMulTest n arity p.1.1 p.1.2 Gamma p.2.1 p.2.2.1 p.2.2.2)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMulPrimrecTargets
