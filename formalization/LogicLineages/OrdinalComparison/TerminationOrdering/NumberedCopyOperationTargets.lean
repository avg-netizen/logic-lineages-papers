module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedCopyOperationDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPackedCodecPrimrecProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedCopyOperationTargets
open Source NumberedRewriteReduction NumberedAuxiliaryCoding NumberedAuxiliaryDecoding
  NumberedCopyCertificate NumberedCopyOperation

/-- The original head-order decision with the entire finite table as input. -/
def ActualHeadAbovePrimitive : Prop :=
  ∀ n : Nat,
    Primrec (fun p : Table n × HeadCode (Fin n) × HeadCode (Fin n) =>
      decide (RecursiveComparison.headAbove (tableAbove p.1)
        (decodeHead p.2.1) (decodeHead p.2.2)))

/-- Structural Copy is primitive recursive on all raw inputs. -/
def ActualAllCopyCodePrimitive : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat),
    Primrec (fun p : (List (Fin n) × List Ty) ×
        (Table n × HeadCode (Fin n)) × Code (Fin n) =>
      copyCode arity p.1.1 p.1.2 p.2.1.1 p.2.1.2 p.2.2)

/-- Exact agreement with the original typed operation, including failure. -/
def ActualCopyCodeCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (symbols : List (Fin n)) (S : List Ty) (table : Table n)
    (g : HeadCode (Fin n)) (q : Packed (Fin n) arity Gamma),
    copyCode arity symbols S table g (termCode q.2) =
      (copyTarget arity symbols S table Gamma (decodeHead g) q).map
        (fun r => termCode r.2)

/-- Genuine packed Copy, jointly in both windows, table, target head and source. -/
def ActualPackedCopyPrimitive : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty),
    Primrec (fun p : (List (Fin n) × List Ty) ×
        (Table n × HeadCode (Fin n)) × Packed (Fin n) arity Gamma =>
      copyTarget arity p.1.1 p.1.2 p.2.1.1 Gamma (decodeHead p.2.1.2) p.2.2)

/-- The unchanged numeric certificate test on all three numeric inputs. -/
def ActualNumericCopyCertificatePrimitive : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty),
    Primrec (fun p : (List (Fin n) × List Ty) × Table n × Nat × Nat × Nat =>
      copyCertificateTest n arity p.1.1 p.1.2 Gamma p.2.1
        p.2.2.1 p.2.2.2.1 p.2.2.2.2)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedCopyOperationTargets
