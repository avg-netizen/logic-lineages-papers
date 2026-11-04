module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniformMulDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniformMulTargets
open Source NumberedRewriteReduction NumberedAuxiliaryCoding NumberedMultisetCertificate
open NumberedMultisetNumeric NumberedMulCertificate NumberedUniformMultiset NumberedUniformMul

/-- Exact calibration to the original typed decision, for every actual input. -/
def ActualRawMulCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Ty)
    (q r : Packed (Fin n) arity Gamma) (certificate : MultisetCertificate n arity Gamma),
    rawMulTest arity symbols S (termCode q.2) (termCode r.2) (certificateData certificate) =
      mulCertificateTest n arity symbols S Gamma q r certificate

def ActualRawMulPrimitive : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat),
    Primrec (fun p : (List (Fin n) × List Ty) ×
        Code (Fin n) × Code (Fin n) × RawCertificate n =>
      rawMulTest arity p.1.1 p.1.2 p.2.1 p.2.2.1 p.2.2.2)

/-- The original decoded Mul-selector leaf, with all contexts and certificate naturals. -/
def ActualMulTestCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Ty)
    (q r : Packed (Fin n) arity Gamma) (certificate : Nat),
    mulTest n arity symbols S Gamma (termCode q.2) (termCode r.2) certificate =
      (decodeCertificate n arity Gamma certificate).any
        (fun data => mulCertificateTest n arity symbols S Gamma q r data)

/-- Gamma varies jointly with the windows, endpoint codes, and certificate number. -/
def ActualMulTestPrimitive : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat),
    Primrec (fun p : (List (Fin n) × List Ty) × List Ty ×
        Code (Fin n) × Code (Fin n) × Nat =>
      mulTest n arity p.1.1 p.1.2 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniformMulTargets
